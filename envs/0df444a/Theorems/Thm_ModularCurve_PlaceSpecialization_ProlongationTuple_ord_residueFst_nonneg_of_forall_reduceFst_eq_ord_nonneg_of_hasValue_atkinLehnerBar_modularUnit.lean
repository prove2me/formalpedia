-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_ord_residueFst_nonneg_of_forall_reduceFst_eq_ord_nonneg_of_hasValue_atkinLehnerBar_modularUnit
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.ord_residueFst_nonneg_of_forall_reduceFst_eq_ord_nonneg_of_hasValue_atkinLehnerBar_modularUnit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:45.66333+00:00
-- url     : https://prove2.me/theorems/0a03bca6-d914-5a67-ac2a-289125e5f7ee
-- title:
--   Regularity of the first residue at affine φ²-fixed places
-- statement:
--   Fix $N \geq 1$ and a prime $q$ with $q \nmid N$, a valuation subring $A$ of $\overline{\mathbb{Q}}$, an algebraically closed field $k$ of characteristic $q$, a ring homomorphism $\mathrm{red} : A \to k$, and modular polynomial data `data` for $q$ satisfying the Kronecker congruence $\overline{\Phi} = (X'^q - X)(X' - X^q)$ modulo $q$; assume the degeneracy embeddings `heckeAlphaBar` and `heckeBetaBar` from level $N$ to level $Nq$ over $\overline{\mathbb{Q}}$ are integral, and that every nonzero element of the level-$Nq$ function field $\overline{\mathbb{Q}}$-field `modularFunctionFieldBar (N * q)` has a degree-zero principal divisor. Let $P$ be a place specialisation for these data and $R$ a prolongation tuple over $P$ satisfying the model laws `IsModel` (the two divisor laws and the two cusp laws) and the law `OrderLawFixed` at Frobenius-fixed affine places. Let $u$ be an element of the level-$Nq$ function field whose underlying Laurent series is the coefficient embedding of the modular unit series $\Delta/\Delta^{(q)}$ of level $q$. Let $g$ lie in the valuation rings `R.R₁.integers` and `R.R₂.integers` of both prolongations, with nonzero first residue $R_1(g) \neq 0$. Let $V_0$ be a place of the level-$Nq$ function field such that its first reduction $v =$ `P.reduceFst V₀`, a place of `modularFunctionFieldC k N`, is fixed by the square of `frobOnPlacesGeomLevel` and is affine, i.e. both $j$ and $j_N$ lie in the valuation ring of $v$; assume every place $W \neq V_0$ with the same first reduction satisfies $\mathrm{ord}_W(g) \geq 0$. Assume finally that for some $a \in A$ with $\mathrm{red}\, a \neq 0$ the Atkin–Lehner transport `atkinLehnerBar N q u` of $u$ lies in the valuation ring of $V_0$ and has residue the image of $a$ there. Then $\mathrm{ord}_v\bigl(R.\mathrm{residue}_1(g)\bigr) \geq 0$, i.e. the first residue of $g$ has no pole at $v$.
--
--   This is one of the local regularity steps in the dictionary between places of the level-$Nq$ modular function field over $\overline{\mathbb{Q}}$ and places of the special fibre in characteristic $q$: the Atkin–Lehner condition at $V_0$ identifies it as a non-cuspidal place on the second sheet, so that the pole of $g$ concentrated there does not propagate to the first residue. It is used by [`ModularCurve.PlaceSpecialization.ProlongationTuple.ord_residueFst_nonneg_of_not_hasValue_modularUnit`](thm.html#ModularCurve.PlaceSpecialization.ProlongationTuple.ord_residueFst_nonneg_of_not_hasValue_modularUnit).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_ord_residueFst_nonneg_of_forall_reduceFst_eq_ord_nonneg_of_hasValue_atkinLehnerBar_modularUnit.lean

import Mathlib
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_ModularCurve_CuspidalClass

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option Elab.async false
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open AlgebraicCurve ModularCurve ModularCurve.PlaceSpecialization

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.ord_residueFst_nonneg_of_forall_reduceFst_eq_ord_nonneg_of_hasValue_atkinLehnerBar_modularUnit
    {N : ℕ} [NeZero N] {q : ℕ} [Fact q.Prime] (hqN : ¬ q ∣ N)
    {A : ValuationSubring (AlgebraicClosure ℚ)} {k : Type*} [Field k]
    [CharP k q] [IsAlgClosed k]
    [HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))]
    {red : A →+* k} {data : ModularPolynomialData q}
    {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (R : ProlongationTuple P) (hR : R.IsModel) (hO : R.OrderLawFixed)
    (u : modularFunctionFieldBar (N * q))
    (hu : (u : LaurentSeries (AlgebraicClosure ℚ))
      = coeffEmb (AlgebraicClosure ℚ) (modularUnitSeries q))
    (g : modularFunctionFieldBar (N * q)) (h₁ : g ∈ R.R₁.integers) (h₂ : g ∈ R.R₂.integers)
    (hres₁ : R.R₁.residue ⟨g, h₁⟩ ≠ 0)
    (V₀ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    (hfix : frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr (P.reduceFst V₀))
      = P.reduceFst V₀)
    (haff : IsAffineGeomPlace k N (P.reduceFst V₀))
    (hpole : ∀ W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
      P.reduceFst W = P.reduceFst V₀ → W ≠ V₀ → 0 ≤ W.ord g)
    (a : A) (ha : red a ≠ 0) (hV₀ : V₀.HasValue (atkinLehnerBar N q u) (a : AlgebraicClosure ℚ)) :
    0 ≤ (P.reduceFst V₀).ord (R.residue₁ ⟨g, h₁⟩) := by sorry
