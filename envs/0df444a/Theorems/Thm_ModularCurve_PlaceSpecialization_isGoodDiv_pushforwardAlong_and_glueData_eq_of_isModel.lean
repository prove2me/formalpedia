-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_isGoodDiv_pushforwardAlong_and_glueData_eq_of_isModel
-- name    : ModularCurve.PlaceSpecialization.isGoodDiv_pushforwardAlong_and_glueData_eq_of_isModel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/37b60b33-b6bb-522d-a762-0fd2bd8fa77a
-- title:
--   Degeneracy pushforward of good divisors and glue data
-- statement:
--   Fix natural numbers $M,s,q'$ with $M,s$ nonzero, $s$ and $q'$ prime, $s\neq q'$ and $q'\nmid M$, and a valuation subring $A$ of $\overline{\mathbb{Q}}$ whose `LiesOverPrime q'` holds, i.e. $q'$ lies in the nonunits of $A$; then the residue field $k=\mathrm{ResidueField}\,A$ has characteristic $q'$. Given modular polynomial data $data_1,data_2$ for $q'$ (monic $\Phi\in\mathbb{Z}[X][Y]$ of degree $\psi(q')$ killing $(j,j_{q'})$) each satisfying the Kronecker congruence $\Phi\equiv(C X^{q'}-X)(C X-X^{q'})\bmod q'$; integrality of the two degeneracy embeddings $\alpha,\beta$ at levels $M\!\cdot\! s$ and $M$; place specialisations $P_1$ at level $M\!\cdot\! s$ and $P_2$ at level $M$ over $A$ with residue map $\mathrm{residue}\,A$, each equipped with a prolongation tuple ($R_1,R_2$) satisfying `IsModel` (the two divisor laws and the two cusp laws) and `OrderLawFixed`; finite sets $S_1,S_2$ of pairs of places of $\mathrm{modularFunctionFieldC}\,k\,(M\!\cdot\! s)$, resp. of level $M$, a map $\nu:S_1\to S_2$ and multiplicities $m:S_1\to\mathbb{N}$; integral $\overline{\mathbb{Q}}$-algebra maps $\delta_0,\delta_1$ from level $M q'$ to level $M s q'$ acting on Laurent series by the identity, resp. by $q\mapsto q^{s}$; integral $k$-algebra maps $\varphi_0,\varphi_1$ from level $M$ to level $M\!\cdot\! s$ pinned the same way; an index $i\in\{0,1\}$; and a divisor $D$ on $\mathrm{modularFunctionFieldBar}(M s q')$ such that for each $W$ in the support of $D$ both reductions $P_1.\mathrm{reduceFst}\,W$ and $P_1.\mathrm{reduceSnd}\,W$, restricted along $\varphi_i$, are moved by the square of `frobOnPlacesGeomLevel` at level $M$ for $data_2$. The conclusion is twofold: the pushforward of $D$ along $\delta_i$ is a good divisor for $P_2$, every place of its support being strict of the first or the second kind; and the glue datum $P_2.\mathrm{glueData}\,S_2$ of that pushforward equals the pushforward along $\varphi_i$, with node map $\nu$ and multiplicities $m$, of the glue datum $P_1.\mathrm{glueData}\,S_1\,D$, i.e. the two strict-part divisors correspond under pushforward of places and the node-unit components agree.
--
--   This is the two-level compatibility step: it transports goodness of a divisor and the associated gluing datum from the degeneracy tower at level $M\cdot s\cdot q'$ down to level $M\cdot q'$, matching the induced identifications of the glued Picard data at levels $M\cdot s$ and $M$. It feeds the glued specialisation statement for the two-level degeneracy glue, used in the level-lowering part of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_isGoodDiv_pushforwardAlong_and_glueData_eq_of_isModel.lean

import Definitions.Def_AlgebraicCurve_GluedPic0Pushforward
import Definitions.Def_ModularCurve_JZeroSemistableSpecialization
import Definitions.Def_ValuationSubring_ReduceAt
import Definitions.Def_ModularCurve_PlaceSpecialization
import Definitions.Def_ModularCurve_GlueData
import Definitions.Def_ModularCurve_ProlongationTuple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option Elab.async false
open AlgebraicCurve IsLocalRing ModularCurve

theorem ModularCurve.PlaceSpecialization.isGoodDiv_pushforwardAlong_and_glueData_eq_of_isModel
    (M s q' : ℕ) [NeZero M] [NeZero s] (hs : s.Prime) (hq' : q'.Prime)
    (hsq' : s ≠ q') (hq'M : ¬ q' ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q') :
    haveI : NeZero q' := ⟨hq'.ne_zero⟩
    haveI : Fact q'.Prime := ⟨hq'⟩
    haveI : CharP (ResidueField A) q' := ValuationSubring.charP_residueField_of_liesOverPrime_def hq' hA
    letI := instDecidableEqResidueFieldSemistable A
    letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A (M * s)
    letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A M
    ∀ (data₁ : ModularPolynomialData q') (hKr₁ : KroneckerCongruence q' data₁)
      (hα₁ : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) (M * s) q')
      (hβ₁ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) (M * s) q')
      (P₁ : PlaceSpecialization A q' (M * s) data₁ hKr₁ (ResidueField A) (IsLocalRing.residue A) hα₁ hβ₁)
      (R₁ : PlaceSpecialization.ProlongationTuple P₁) (hmodel₁ : R₁.IsModel) (hO₁ : R₁.OrderLawFixed)
      (data₂ : ModularPolynomialData q') (hKr₂ : KroneckerCongruence q' data₂)
      (hα₂ : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) M q')
      (hβ₂ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) M q')
      (P₂ : PlaceSpecialization A q' M data₂ hKr₂ (ResidueField A) (IsLocalRing.residue A) hα₂ hβ₂)
      (R₂ : PlaceSpecialization.ProlongationTuple P₂) (hmodel₂ : R₂.IsModel) (hO₂ : R₂.OrderLawFixed)
      (S₁ : Finset (Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) (M * s)) × Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) (M * s))))
      (S₂ : Finset (Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) M) × Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) M))) [DecidableEq ↥S₂]
      (ν : ↥S₁ → ↥S₂) (m : ↥S₁ → ℕ)
      (δ : Fin 2 → (↥(modularFunctionFieldBar (M * q')) →ₐ[AlgebraicClosure ℚ] ↥(modularFunctionFieldBar (M * s * q'))))
      (hδ : ∀ i, (δ i).toRingHom.IsIntegral)
      (hδα : ∀ x, ((δ 0 x : ↥(modularFunctionFieldBar (M * s * q'))) : LaurentSeries (AlgebraicClosure ℚ)) = x)
      (hδβ : ∀ x, ((δ 1 x : ↥(modularFunctionFieldBar (M * s * q'))) : LaurentSeries (AlgebraicClosure ℚ)) =
        qExpand (AlgebraicClosure ℚ) s x)
      (φ : Fin 2 → (↥(modularFunctionFieldC (ResidueField A) M) →ₐ[ResidueField A] ↥(modularFunctionFieldC (ResidueField A) (M * s))))
      (hφ : ∀ i, (φ i).toRingHom.IsIntegral)
      (hφα : ∀ x, ((φ 0 x : ↥(modularFunctionFieldC (ResidueField A) (M * s))) : LaurentSeries (ResidueField A)) = x)
      (hφβ : ∀ x, ((φ 1 x : ↥(modularFunctionFieldC (ResidueField A) (M * s))) : LaurentSeries (ResidueField A)) =
        qExpand (ResidueField A) s x)
      (i : Fin 2) (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (M * s * q')))
      (hclean : ∀ W ∈ D.support,
        frobOnPlacesGeomLevel (ResidueField A) M data₂ hKr₂
            (frobOnPlacesGeomLevel (ResidueField A) M data₂ hKr₂ ((P₁.reduceFst W).restrictAlong (φ i) (hφ i))) ≠
          (P₁.reduceFst W).restrictAlong (φ i) (hφ i) ∧
        frobOnPlacesGeomLevel (ResidueField A) M data₂ hKr₂
            (frobOnPlacesGeomLevel (ResidueField A) M data₂ hKr₂ ((P₁.reduceSnd W).restrictAlong (φ i) (hφ i))) ≠
          (P₁.reduceSnd W).restrictAlong (φ i) (hφ i)),
      P₂.IsGoodDiv (Divisor.pushforwardAlong (δ i) (hδ i) D) ∧
        P₂.glueData S₂ (Divisor.pushforwardAlong (δ i) (hδ i) D) =
          GluingData.pushforwardMap S₁ S₂ ν m (φ i) (hφ i) (P₁.glueData S₁ D) := by sorry
