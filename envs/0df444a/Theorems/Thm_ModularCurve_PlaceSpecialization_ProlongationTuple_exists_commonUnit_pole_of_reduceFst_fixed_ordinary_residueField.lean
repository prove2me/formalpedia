-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_commonUnit_pole_of_reduceFst_fixed_ordinary_residueField
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.exists_commonUnit_pole_of_reduceFst_fixed_ordinary_residueField
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:45.66333+00:00
-- url     : https://prove2.me/theorems/5906830b-9379-5cf4-9034-71751d13ba2c
-- title:
--   Common unit with simple pole over an ordinary Frobenius-fixed place
-- statement:
--   Let $q$ be a prime and let $A$ be a valuation subring of $\overline{\mathbb Q}$ lying over $q$, in the sense that $q$ is a non-unit of $A$; then the residue field $k = \mathrm{ResidueField}\,A$ has characteristic $q$. Let $N$ be nonzero. Consider modular polynomial data `data` for $q$ (a monic $\Phi \in \mathbb{Z}[X][Y]$ of degree $\psi(q)$ annihilating the pair $(j, j_q)$) satisfying the Kronecker congruence, that the reduction of $\Phi$ modulo $q$ is $(C X^{q} - X)(C X - X^{q})$; integrality hypotheses $h\alpha$, $h\beta$ for the two degeneracy embeddings `heckeAlphaBar`, `heckeBetaBar` of level $N$ into level $Nq$; a place specialization $P$ over $k$ with reduction map the residue map of $A$; and a prolongation tuple $R$ for $P$ satisfying `IsModel` (the two divisor laws and the two cusp laws) and `OrderLawFixed`. Assume $q \nmid N$, and let $V_0$ be a place of the level-$Nq$ function field $\mathrm{modularFunctionFieldBar}(N q)$ over $\overline{\mathbb Q}$ whose first reduction $v = P.\mathrm{reduceFst}\,V_0$ is fixed by the square of the geometric-level Frobenius map on places, is affine (both $j$ and $j_N$ generators lie in its valuation subring) and is not a supersingular place. Then for every finite set $S \subseteq k$ and every finite set $B$ of places of the level-$N$ function field $\mathrm{modularFunctionFieldC}\,k\,N$ there is $g$ in the level-$Nq$ function field, lying in the valuation subrings of both prolongations $R.R_1$, $R.R_2$ and with nonzero residue under both, such that $\mathrm{ord}_{V_0}(g) = -1$, such that every other pole $V \neq V_0$ of $g$ is good, namely $\mathrm{ord}_V(j - a) > 0$ for some $a \in A$ whose residue avoids $S$, and both $P.\mathrm{reduceFst}\,V$ and $P.\mathrm{reduceSnd}\,V$ avoid $B$; and finally either $\mathrm{ord}_v(R.\mathrm{residue}_1 g) = -1$ and $\mathrm{ord}_{\mathrm{Frob}(v)}(R.\mathrm{residue}_2 g) = 0$, or $\mathrm{ord}_v(R.\mathrm{residue}_1 g) = 0$ and $\mathrm{ord}_{\mathrm{Frob}(v)}(R.\mathrm{residue}_2 g) = -1$.
--
--   This is the level-$N$ form, with constant field the residue field of $A$ and reduction map the residue map of $A$, of the construction of a function with a single prescribed simple pole whose pole survives on exactly one of the two components of the semistable fibre of $X_0(Nq)$ at $q$. It feeds the computation of the first-sheet divisor law at places fixed by the square of Frobenius.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_commonUnit_pole_of_reduceFst_fixed_ordinary_residueField.lean

import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_JZeroSemistableSpecialization
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_WeierstrassCurve_ReductionMap

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option Elab.async false
set_option autoImplicit false
open IsLocalRing
open AlgebraicCurve ModularCurve ModularCurve.PlaceSpecialization.ProlongationTuple
open ModularCurve.PlaceSpecialization hiding jFun

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.exists_commonUnit_pole_of_reduceFst_fixed_ordinary_residueField
    (q : ℕ) (hq : q.Prime) (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) (N : ℕ) [NeZero N] :
    haveI : NeZero q := ⟨hq.ne_zero⟩
    haveI : Fact q.Prime := ⟨hq⟩
    haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
    letI := heckeModuleBar (N * q)
    letI := heckeModuleBar N
    letI := instDecidableEqResidueFieldSemistable A
    letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
    ∀ (data : ModularPolynomialData q) (hKr : KroneckerCongruence q data)
      (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q) (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q)
      (P : PlaceSpecialization A q N data hKr (ResidueField A) (IsLocalRing.residue A) hα hβ) (R : ProlongationTuple P)
      (hR : R.IsModel) (hO : R.OrderLawFixed) (hqN : ¬ q ∣ N)
      (V₀ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
      (hfix : frobOnPlacesGeomLevel (ResidueField A) N data hKr (frobOnPlacesGeomLevel (ResidueField A) N data hKr
          (P.reduceFst V₀))
        = P.reduceFst V₀)
      (haff : IsAffineGeomPlace (ResidueField A) N (P.reduceFst V₀))
      (hord : P.reduceFst V₀ ∉ ssPlaces q N (ResidueField A)) (S : Finset (ResidueField A))
      (B : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N))),
    ∃ (g : modularFunctionFieldBar (N * q)) (h₁ : g ∈ R.R₁.integers) (h₂ : g ∈ R.R₂.integers),
      R.R₁.residue ⟨g, h₁⟩ ≠ 0 ∧ R.R₂.residue ⟨g, h₂⟩ ≠ 0 ∧ V₀.ord g = -1 ∧
      (∀ V, V ≠ V₀ → V.ord g < 0 →
        (∃ a : A, 0 < V.ord (jFun N q - algebraMap (AlgebraicClosure ℚ)
            (modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ)) ∧ (IsLocalRing.residue A) a ∉ S) ∧
          P.reduceFst V ∉ B ∧ P.reduceSnd V ∉ B) ∧
      (((P.reduceFst V₀).ord (R.residue₁ ⟨g, h₁⟩) = -1 ∧
          (frobOnPlacesGeomLevel (ResidueField A) N data hKr (P.reduceFst V₀)).ord (R.residue₂ ⟨g, h₂⟩) = 0) ∨
        ((P.reduceFst V₀).ord (R.residue₁ ⟨g, h₁⟩) = 0 ∧
          (frobOnPlacesGeomLevel (ResidueField A) N data hKr (P.reduceFst V₀)).ord (R.residue₂ ⟨g, h₂⟩) = -1)) := by sorry
