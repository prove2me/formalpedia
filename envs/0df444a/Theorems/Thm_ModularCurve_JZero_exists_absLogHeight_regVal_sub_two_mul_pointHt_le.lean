-- Prove2me | Theorems.Thm_ModularCurve_JZero_exists_absLogHeight_regVal_sub_two_mul_pointHt_le
-- name    : ModularCurve.JZero.exists_absLogHeight_regVal_sub_two_mul_pointHt_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:41.339792+00:00
-- url     : https://prove2.me/theorems/830b2039-d3db-5d23-802c-f4ada0fbce63
-- title:
--   Tangent datum height exceeds 2h(P) by (2g-2+ε)t(P)+C
-- statement:
--   Fix $N \ge 1$ and work with $F =$ `modularFunctionFieldBar N`, the base change to $\overline{\mathbb Q}$ of the full modular function field of level $N$ inside $\overline{\mathbb Q}$-Laurent series. Let $s : \mathrm{Fin}\,r \to F$ satisfy `IsEmbBasis N s`, i.e. $s$ is linearly independent over $\overline{\mathbb Q}$ and its range spans `riemannRochSpace (embDivisor N)`; assume $1 \le g$, where $g =$ `genusFF` $= \dim_{\overline{\mathbb Q}} H^1(0)$ for $F$, and let $\varepsilon > 0$. The assertion is that there is a real constant $C$, independent of everything below, such that for every place $P$ of $F$ over $\overline{\mathbb Q}$ (a proper valuation subring containing the constants, with principal ideals) with $P \ne$ `cuspInftyBar N`, and every $t \in F$ with $\mathrm{ord}_P(t) = 1$, one has $h(y_P) - 2\,h(P) \le (2g - 2 + \varepsilon)\,b(P) + C$. Here $h(P) =$ `pointHt s P` is the absolute logarithmic height `absLogHeight` of the vector $\bigl(P(s_i s_{\pi}^{-1})\bigr)_i$ of values at $P$ in the pivot trivialisation ($\pi =$ `pivotIndex s P`), $y_P$ is the family indexed by $\mathrm{Fin}\,r \times \mathrm{Fin}\,r$ whose $(i,j)$ entry is the value at $P$ of $\bigl(P(s_i s_\pi^{-1})\,s_j - P(s_j s_\pi^{-1})\,s_i\bigr)\,s_\pi^{-1} t^{-1}$, $h(y_P) =$ `absLogHeight` of that family, and $b(P) =$ `baseHt s (cuspInftyBar N) P`, which for $P \ne$ `cuspInftyBar N` is `pairHt s P (cuspInftyBar N)`.
--
--   This is the derivative, or tangent-datum, cost in the Weil height machine on the modular curve: the order-one regularised values of the chord functions through $P$ have height exceeding twice the height of $P$ only by $(2g-2+\varepsilon)$ times the proximity of $P$ to the cusp at infinity, plus a bounded error. It feeds the height-form estimates on $\mathrm{Pic}^0$ of the modular function field, being used by [`ModularCurve.JZero.exists_baseMass_le_heightForm_of_exists_two_le`](thm.html#ModularCurve.JZero.exists_baseMass_le_heightForm_of_exists_two_le).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZero_exists_absLogHeight_regVal_sub_two_mul_pointHt_le.lean

import Definitions.Def_ModularCurve_JZeroHeightForm
import Definitions.Def_AlgebraicCurve_ChordalProximity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve
open AlgebraicCurve

theorem ModularCurve.JZero.exists_absLogHeight_regVal_sub_two_mul_pointHt_le (N : ℕ) [NeZero N] {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s)
    (hg : 1 ≤ genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, ∀ (P : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (t : modularFunctionFieldBar N),
      P ≠ cuspInftyBar N → P.ord t = 1 →
        absLogHeight (fun p : Fin r × Fin r =>
            regVal s P t 1 1 (evalVec s P p.1 • s p.2 - evalVec s P p.2 • s p.1))
          - 2 * pointHt s P
        ≤ (2 * (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) : ℝ) - 2 + ε)
            * baseHt s (cuspInftyBar N) P + C := by sorry
