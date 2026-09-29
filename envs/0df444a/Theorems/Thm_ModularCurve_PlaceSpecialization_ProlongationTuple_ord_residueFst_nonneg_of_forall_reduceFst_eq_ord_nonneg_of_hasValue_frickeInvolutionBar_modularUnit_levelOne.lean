-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_ord_residueFst_nonneg_of_forall_reduceFst_eq_ord_nonneg_of_hasValue_frickeInvolutionBar_modularUnit_levelOne
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.ord_residueFst_nonneg_of_forall_reduceFst_eq_ord_nonneg_of_hasValue_frickeInvolutionBar_modularUnit_levelOne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:45.66333+00:00
-- url     : https://prove2.me/theorems/f0f9b2e1-776d-570d-81f9-083ec0fed8ad
-- title:
--   Regularity of the first residue at a second-sheet place
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q}$, an algebraically closed field $k$ of characteristic $q$, a ring homomorphism $\mathrm{red}\colon A\to k$, and modular polynomial data `data` for $q$ (a monic $\Phi\in\mathbb Z[X][Y]$ of degree $\psi(q)$ annihilating the pair $(j,j_q)$) satisfying the Kronecker congruence `hKr`, namely that the reduction of $\Phi$ modulo $q$ is $(X^q-Y)(X-Y^q)$; assume further that the level-$1$ Hecke maps $\bar\alpha$ and $\bar\beta$ for $q$ are integral ring homomorphisms ($h\alpha$, $h\beta$). Let $P$ be a place specialisation for these data and $R$ a prolongation tuple over $P$, with regular prolongations $R_1,R_2$ of $A$ in $\overline{\mathbb Q}(X_0(1\cdot q))=$ `modularFunctionFieldBar (1 * q)`. Let $u$ be an element of that field whose Laurent expansion is the coefficientwise image of `modularUnitSeries q` $=\Delta\cdot\Delta(q\,\cdot)^{-1}$. Let $g$ lie in the integers of both $R_1$ and $R_2$, with $R_1$-residue non-zero. Let $V_0$ be a place of `modularFunctionFieldBar (1 * q)` over $\overline{\mathbb Q}$, and write $v=P.\mathrm{reduceFst}\,V_0$ for the place of `modularFunctionFieldC k 1` obtained by restricting $V_0$ along $\bar\alpha$ and specialising by $P.\mathrm{sp}$. Assume: $v$ is fixed by the square of the geometric-level Frobenius `frobOnPlacesGeomLevel`; $v$ is affine, i.e. both $j$ and $j_N$ (the generators `jGeomGen`, `jNGeomGen`) lie in its valuation subring; every place $W\neq V_0$ with $P.\mathrm{reduceFst}\,W=v$ satisfies $\mathrm{ord}_W(g)\ge 0$; and there is $a\in A$ with $\mathrm{red}\,a\neq 0$ such that $V_0$ has value $a$ at $\mathrm{frickeInvolutionBar}(1\cdot q)(u)$, that is, this element lies in the valuation subring of $V_0$ and its residue is the image of $a$. Then $\mathrm{ord}_v$ of the first-prolongation residue $R.\mathrm{residue}_1\langle g,h_1\rangle$, an element of `modularFunctionFieldC k 1`, is $\ge 0$.
--
--   This is the second-sheet counterpart of the first-sheet regularity statement in the analysis of the reduction of $X_0(q)$ modulo $q$: at an affine place of the special fibre fixed by the square of Frobenius, a function integral for both Gauss prolongations whose only pole above that place sits on the sheet where the modular unit $\Delta/\Delta(q\,\cdot)$ becomes a unit after the Fricke involution has regular first residue. It is used in computing the divisor of the first residue, in [`ModularCurve.PlaceSpecialization.ProlongationTuple.mapDomain_reduceFst_filter_sheetOne_eq_ord_residueFst_levelOne_univ`](thm.html#ModularCurve.PlaceSpecialization.ProlongationTuple.mapDomain_reduceFst_filter_sheetOne_eq_ord_residueFst_levelOne_univ).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_ord_residueFst_nonneg_of_forall_reduceFst_eq_ord_nonneg_of_hasValue_frickeInvolutionBar_modularUnit_levelOne.lean

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

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.ord_residueFst_nonneg_of_forall_reduceFst_eq_ord_nonneg_of_hasValue_frickeInvolutionBar_modularUnit_levelOne
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
    (hres₁ : R.R₁.residue ⟨g, h₁⟩ ≠ 0)
    (V₀ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)))
    (hfix : frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr (P.reduceFst V₀))
      = P.reduceFst V₀)
    (haff : IsAffineGeomPlace k 1 (P.reduceFst V₀))
    (hpole : ∀ W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)),
      P.reduceFst W = P.reduceFst V₀ → W ≠ V₀ → 0 ≤ W.ord g)
    (a : A) (ha : red a ≠ 0) (hV₀ : V₀.HasValue (frickeInvolutionBar (1 * q) u) (a : AlgebraicClosure ℚ)) :
    0 ≤ (P.reduceFst V₀).ord (R.residue₁ ⟨g, h₁⟩) := by sorry
