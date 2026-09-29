-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_sp_restrictAlong_eq_restrictAlong_sp_of_isModel
-- name    : ModularCurve.PlaceSpecialization.sp_restrictAlong_eq_restrictAlong_sp_of_isModel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/44555941-b878-559c-824a-ef2ed5afb656
-- title:
--   Specialization commutes with degeneracy restriction off Frobenius-fixed places
-- statement:
--   Fix natural numbers $M, s, q'$ with $M, s$ nonzero, $s$ and $q'$ prime, $s \neq q'$ and $q' \nmid M$, and a valuation subring $A$ of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` such that $q'$ is a nonunit of $A$; consequently the residue field $k =$ `ResidueField A` has characteristic $q'$. Given: modular polynomial data `data₁`, `data₂` for $q'$ (each a monic $\Phi \in \mathbb{Z}[X][Y]$ of degree $\psi(q')$ annihilating $(j(q), j(q^{q'}))$) satisfying the Kronecker congruence $\Phi \equiv (X^{q'} - Y)(X - Y^{q'}) \bmod q'$; integrality of the two degeneracy maps $\bar\alpha, \bar\beta$ at levels $M \cdot s$ and $M$; place-specialization packages $P_1$ at level $M\cdot s$ and $P_2$ at level $M$, both with target $k$ and reduction map the residue map of $A$; and for each a prolongation tuple $R_i$ satisfying `IsModel` (the two divisor laws and the cusp laws at $\infty$ and at $0$) together with `OrderLawFixed`. Given further $\overline{\mathbb{Q}}$-algebra maps $\delta_0, \delta_1 : \overline{M}_M \to \overline{M}_{M\cdot s}$ between the base-changed modular function fields, both integral, with $\delta_0$ acting as the identity and $\delta_1$ as $q \mapsto q^s$ on $q$-expansions, and $k$-algebra maps $\varphi_0, \varphi_1$ between the characteristic-$q'$ modular function fields of levels $M$ and $M \cdot s$, both integral, with the same effect on Laurent expansions. Then for each $i \in \{0,1\}$ and each place $v$ of $\overline{M}_{M \cdot s}$ over $\overline{\mathbb{Q}}$: if the place $(P_1.\mathrm{sp}\, v)$ restricted along $\varphi_i$ (the valuation subring pulled back along $\varphi_i$) is not fixed by the square of `frobOnPlacesGeomLevel` at level $M$ for `data₂`, then $P_2.\mathrm{sp}$ of $v$ restricted along $\delta_i$ equals $(P_1.\mathrm{sp}\, v)$ restricted along $\varphi_i$.
--
--   This is the level compatibility of the mod-$q'$ place-specialization packages: the two degeneracy maps between levels $M$ and $M\cdot s$ commute with specialization, away from the places of the level-$M$ special fibre fixed by the square of the geometric Frobenius. It feeds the construction identifying the glue data and the good divisors attached to the pushforward along the degeneracy maps, in [`ModularCurve.PlaceSpecialization.isGoodDiv_pushforwardAlong_and_glueData_eq_of_isModel`](thm.html#ModularCurve.PlaceSpecialization.isGoodDiv_pushforwardAlong_and_glueData_eq_of_isModel).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_sp_restrictAlong_eq_restrictAlong_sp_of_isModel.lean

import Definitions.Def_ModularCurve_JZeroSemistableSpecialization
import Definitions.Def_ValuationSubring_ReduceAt
import Definitions.Def_ModularCurve_PlaceSpecialization
import Definitions.Def_ModularCurve_ProlongationTuple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option Elab.async false
open IsLocalRing ModularCurve
open AlgebraicCurve

theorem ModularCurve.PlaceSpecialization.sp_restrictAlong_eq_restrictAlong_sp_of_isModel
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
      (δ : Fin 2 → (↥(modularFunctionFieldBar M) →ₐ[AlgebraicClosure ℚ] ↥(modularFunctionFieldBar (M * s))))
      (hδ : ∀ i, (δ i).toRingHom.IsIntegral)
      (hδα : ∀ x, ((δ 0 x : ↥(modularFunctionFieldBar (M * s))) : LaurentSeries (AlgebraicClosure ℚ)) = x)
      (hδβ : ∀ x, ((δ 1 x : ↥(modularFunctionFieldBar (M * s))) : LaurentSeries (AlgebraicClosure ℚ)) =
        qExpand (AlgebraicClosure ℚ) s x)
      (φ : Fin 2 → (↥(modularFunctionFieldC (ResidueField A) M) →ₐ[ResidueField A] ↥(modularFunctionFieldC (ResidueField A) (M * s))))
      (hφ : ∀ i, (φ i).toRingHom.IsIntegral)
      (hφα : ∀ x, ((φ 0 x : ↥(modularFunctionFieldC (ResidueField A) (M * s))) : LaurentSeries (ResidueField A)) = x)
      (hφβ : ∀ x, ((φ 1 x : ↥(modularFunctionFieldC (ResidueField A) (M * s))) : LaurentSeries (ResidueField A)) = qExpand (ResidueField A) s x),
    ∀ (i : Fin 2) (v : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (M * s))),
      frobOnPlacesGeomLevel (ResidueField A) M data₂ hKr₂
          (frobOnPlacesGeomLevel (ResidueField A) M data₂ hKr₂ ((P₁.sp v).restrictAlong (φ i) (hφ i))) ≠
        (P₁.sp v).restrictAlong (φ i) (hφ i) →
      P₂.sp (v.restrictAlong (δ i) (hδ i)) = (P₁.sp v).restrictAlong (φ i) (hφ i) := by sorry
