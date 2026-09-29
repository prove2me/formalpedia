-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_mapDomain_restrictAlong_filter_isInftySide_divisor_modularUnit
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.mapDomain_restrictAlong_filter_isInftySide_divisor_modularUnit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:45.66333+00:00
-- url     : https://prove2.me/theorems/879ab584-1dfc-590e-85a7-79a819c6ed5a
-- title:
--   Push-forward of the ∞-side divisor of the modular unit
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb{Q}}=$ `AlgebraicClosure ℚ`, a positive integer $N$, a field $k$ of characteristic $q$ and a ring homomorphism $\mathrm{red} : A \to k$; fix further a `ModularPolynomialData` for $q$, i.e. a monic polynomial $\Phi \in \mathbb{Z}[X][Y]$ of degree $\psi(q)$ annihilating the pair $(j,j_q)$ of $q$-expansions, together with the hypothesis `KroneckerCongruence` that its reduction modulo $q$ is $(X^q - Y)(X - Y^q)$, and the hypotheses $h\alpha$, $h\beta$ that the two degeneracy inclusions `heckeAlphaBar`, `heckeBetaBar` from level $N$ to level $Nq$ (between the base changes to $\overline{\mathbb{Q}}$ of the full modular function fields inside Laurent series) are integral ring maps. Assume $q \nmid N$, and let $P$ be a `PlaceSpecialization` of level $N$ at $q$ over $(A,\mathrm{red},k)$. Let $u$ be an element of `modularFunctionFieldBar (N * q)` whose underlying Laurent series is the coefficientwise image of the modular unit $\Delta/\Delta_q$ `modularUnitSeries q`, let $D$ be the divisor on level $Nq$ with $D(W) = \mathrm{ord}_W(u)$ at every place $W$, and let $D_j$ be the divisor on level $N$ with $D_j(b) = \mathrm{ord}_b(j)$, $j$ being the image of the $q$-expansion `jq`. Then for every place $b$ of `modularFunctionFieldBar N`, the push-forward along $W \mapsto W$ restricted along `heckeAlphaBar` of the restriction of $D$ to the places $W$ satisfying `IsInftySide P` (that is, $W$ is cuspidal for $P$ and $W$ takes at `tInfty N q` a value $\tau \in A$ with $\mathrm{red}(\tau) = 1$) takes at $b$ the value $(q-1)$ times the value at $b$ of the restriction of $D_j$ to the places where $D_j$ is negative.
--
--   This is the computation of the $\infty$-side contribution to the divisor of the level-$q$ modular unit $\Delta/\Delta_q$ on $X_0(Nq)$: under push-forward along the first degeneracy map it becomes $(q-1)$ times the polar part of the divisor of $j$ at level $N$, the pole order of $j$ at a cusp recording its width. It feeds the construction of the one-sided divisor laws for the modular unit used in the analysis of the reduction of $X_0(Nq)$ at $q$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_mapDomain_restrictAlong_filter_isInftySide_divisor_modularUnit.lean

import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_ModularCurve_LaurentCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option Elab.async false
set_option synthInstance.maxHeartbeats 400000
open AlgebraicCurve ModularCurve
open Classical in

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.mapDomain_restrictAlong_filter_isInftySide_divisor_modularUnit
    {q : ℕ} [Fact q.Prime]
    {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N] {k : Type*} [Field k]
    [CharP k q] {red : A →+* k} {data : ModularPolynomialData q}
    {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    (hqN : ¬ q ∣ N)
    (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (u : modularFunctionFieldBar (N * q))
    (hu : (u : LaurentSeries (AlgebraicClosure ℚ))
      = coeffEmb (AlgebraicClosure ℚ) (modularUnitSeries q))
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) (hD : ∀ W, D W = W.ord u)
    (Dj : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hDj : ∀ b : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      Dj b = b.ord ⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
          (modularFunctionField_le_full N (jq_mem N))⟩)
    (b : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :
    Finsupp.mapDomain (fun W => W.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα)
        (D.filter (IsInftySide P)) b
      = ((q : ℤ) - 1) * (Dj.filter (fun b' => Dj b' < 0)) b := by sorry
