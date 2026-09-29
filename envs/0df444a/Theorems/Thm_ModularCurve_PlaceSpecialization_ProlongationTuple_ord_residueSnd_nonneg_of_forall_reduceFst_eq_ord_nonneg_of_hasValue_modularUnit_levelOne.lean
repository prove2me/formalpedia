-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_ord_residueSnd_nonneg_of_forall_reduceFst_eq_ord_nonneg_of_hasValue_modularUnit_levelOne
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.ord_residueSnd_nonneg_of_forall_reduceFst_eq_ord_nonneg_of_hasValue_modularUnit_levelOne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:45.66333+00:00
-- url     : https://prove2.me/theorems/b3eb3553-e1de-5f58-96e5-28e10a4124fe
-- title:
--   Regularity of the second residue at φ v
-- statement:
--   Let $q$ be a prime, $A$ a valuation subring of $\overline{\mathbb Q}$, $k$ an algebraically closed field of characteristic $q$ and $\mathrm{red} : A \to k$ a ring homomorphism; let `data` be a `ModularPolynomialData q`, that is a monic $\Phi \in \mathbb Z[X][Y]$ of degree $\psi(q)$ annihilating the pair $(j, j(q\,\cdot))$ of $q$-expansions, let `hKr` assert that the reduction of $\Phi$ modulo $q$ is $(C X^{q} - X)(C X - X^{q})$, and let `hα`, `hβ` assert that the two degeneracy maps `heckeAlphaBar`, `heckeBetaBar` at level $(1,q)$ over $\overline{\mathbb Q}$ are integral ring homomorphisms. Let $P$ be a place specialization `PlaceSpecialization A q 1 data hKr k red hα hβ` and $R$ a `ProlongationTuple P`, with its two regular prolongations $R_1$, $R_2$ of $A$ to the function field `modularFunctionFieldBar (1 * q)`. Let $u$ be an element of `modularFunctionFieldBar (1 * q)` whose underlying Laurent series is the image under `coeffEmb` of the modular unit $\Delta \cdot (\Delta_q)^{-1}$, and let $g$ be an element of the same field lying in the integers of both $R_1$ and $R_2$, with $R_2$-residue $R_1$ `R.R₂.residue ⟨g, h₂⟩ ≠ 0`. Let $V_0$ be a place of `modularFunctionFieldBar (1 * q)` over $\overline{\mathbb Q}$ such that: the geometric place $v =$ `P.reduceFst V₀` of `modularFunctionFieldC k 1` (obtained by restricting $V_0$ along `heckeAlphaBar` and applying `P.sp`) is fixed by the square of `frobOnPlacesGeomLevel k 1 data hKr`; $v$ is affine, in the sense that both `jGeomGen k 1` and `jNGeomGen k 1` lie in its valuation subring; every place $W \neq V_0$ with `P.reduceFst W = P.reduceFst V₀` satisfies $0 \le \operatorname{ord}_W g$; and there is $a \in A$ with $\mathrm{red}\,a \neq 0$ such that $u$ lies in the valuation subring of $V_0$ with residue the image of $a$ in the residue field of $V_0$. Then the order of the second residue `R.residue₂ ⟨g, h₂⟩` of $g$ at the place `frobOnPlacesGeomLevel k 1 data hKr (P.reduceFst V₀)` is at least $0$, that is, this residue has no pole at the Frobenius image of $v$.
--
--   This is a regularity statement for the Atkin–Lehner (second) Gauss prolongation in the dictionary between places of $\overline{\mathbb Q}(X_0(q))$ and the two components of $X_0(q)$ in characteristic $q$, in the shape used for places lying on the sheet through the cusp, where the modular unit takes a unit value. It feeds the computation of first-sheet contributions in [`ModularCurve.PlaceSpecialization.ProlongationTuple.mapDomain_reduceFst_filter_sheetOne_eq_ord_residueFst_levelOne_univ`](thm.html#ModularCurve.PlaceSpecialization.ProlongationTuple.mapDomain_reduceFst_filter_sheetOne_eq_ord_residueFst_levelOne_univ).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_ord_residueSnd_nonneg_of_forall_reduceFst_eq_ord_nonneg_of_hasValue_modularUnit_levelOne.lean

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

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.ord_residueSnd_nonneg_of_forall_reduceFst_eq_ord_nonneg_of_hasValue_modularUnit_levelOne
    {q : ℕ} [Fact q.Prime]
    {A : ValuationSubring (AlgebraicClosure ℚ)} {k : Type*} [Field k]
    [CharP k q] [DecidableEq k] [IsAlgClosed k]
    {red : A →+* k} {data : ModularPolynomialData q}
    {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    (R : ProlongationTuple P)
    (u : modularFunctionFieldBar (1 * q))
    (hu : (u : LaurentSeries (AlgebraicClosure ℚ))
      = coeffEmb (AlgebraicClosure ℚ) (modularUnitSeries q))
    (g : modularFunctionFieldBar (1 * q)) (h₁ : g ∈ R.R₁.integers) (h₂ : g ∈ R.R₂.integers)
    (hres₂ : R.R₂.residue ⟨g, h₂⟩ ≠ 0)
    (V₀ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)))
    (hfix : frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr (P.reduceFst V₀))
      = P.reduceFst V₀)
    (haff : IsAffineGeomPlace k 1 (P.reduceFst V₀))
    (hpole : ∀ W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)),
      P.reduceFst W = P.reduceFst V₀ → W ≠ V₀ → 0 ≤ W.ord g)
    (a : A) (ha : red a ≠ 0) (hV₀ : V₀.HasValue u (a : AlgebraicClosure ℚ)) :
    0 ≤ (frobOnPlacesGeomLevel k 1 data hKr (P.reduceFst V₀)).ord (R.residue₂ ⟨g, h₂⟩) := by sorry
