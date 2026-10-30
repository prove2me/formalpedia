-- Prove2me | Theorems.Thm_HuangYin_transparent_benchmark
-- name    : HuangYin.transparent_benchmark
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T23:48:48.24484+00:00
-- url     : https://prove2.me/theorems/7d1ece6f-729f-4eb2-a509-7f4c46f16b7e
-- title:
--   Transparent-selling benchmark (corrected: $\max\{v_H-c_H,v_L-c_L\}\ge0$)
-- statement:
--   1. if $\max\{v_H-c_H,\,v_L-c_L\}\ge0$, every transparent policy earns at most $2\max\{v_H-c_H,\,v_L-c_L\}$ over the two periods;
--   2. if $v_H-c_H\ge v_L-c_L$, selling product $H$ at price $v_H$ in both periods earns $2(v_H-c_H)$;
--   3. if $v_L-c_L\ge v_H-c_H$, selling product $L$ at price $v_L$ in both periods earns $2(v_L-c_L)$.
--
--   So the optimal transparent policy sells the product with the larger margin at its valuation. This is the benchmark against which Proposition 1 compares probabilistic selling.
--
--   Differences from the source:
--
--   - correction: no sign condition on the margins → hypothesis 0 ≤ max{vH − cH, vL − cL} on the upper bound (the two profit values carry none); reason: false as printed: at vH = 3, vL = 1, cH = 4, cL = 2 the printed optimum is 2 max = −2, but a price above both valuations sells nothing and earns 0
--   - reading: 'the optimal product offering decisions are' / 'it is optimal to use' → the stated choice is feasible and attains the maximum (`OptimalOffer`, `IsOptimal`), not that it is the unique maximizer; reason: Proposition 1 (iii) calls both transparent policies optimal when vH − cH = vL − cL, so optimality cannot mean uniqueness
--   - generalization: transparent selling of one product, H at pH = vH or L at pL = vL, in both periods (§3.3, p. 11) → transparent policies choosing any product and any price separately in each period; reason: the Lean family contains the paper's two policies; offering both products at once adds nothing because customers are identical
--   - reading: a customer buying product m obtains net utility v_m − p (§3.3) → the whole unit mass buys iff p ≤ v_m; reason: customers buy when their net utility is nonnegative, the same weak inequality as rule (1)
-- source:
--   Huang and Yin, Dynamic Probabilistic Selling When Customers Have Boundedly Rational Expectations, SSRN manuscript 3627927 (2020), §3.3 Benchmark, p. 11 (unnumbered)

import Mathlib
import Definitions.Def_HuangYin_transparentProfit

namespace HuangYin

/-- **The transparent-selling benchmark** (§3.3, p. 11; unnumbered), corrected by the hypothesis
`0 ≤ max{vH − cH, vL − cL}`.
Huang and Yin, *Dynamic Probabilistic Selling When Customers Have Boundedly Rational
Expectations*, SSRN manuscript 3627927 (2020), §3.3, p. 11: "the optimal transparent selling policy for the firm is: (i) Only selling
product H to earn the profit 2(vH − cH) from the two-period selling if vH − cH ≥ vL − cL;
(ii) Only selling product L to earn the profit 2(vL − cL) from the two-period selling if
vH − cH ≤ vL − cL."

If `max{vH − cH, vL − cL} ≥ 0`, every transparent policy earns at most `2 max{vH − cH, vL − cL}`;
selling `H` at `vH` in both periods earns `2(vH − cH)`, and selling `L` at `vL` in both periods
earns `2(vL − cL)`.

**Formalization Note.** The hypothesis `0 ≤ max{vH − cH, vL − cL}` is a correction: if both
margins are negative (vH = 3, vL = 1, cH = 4, cL = 2), a price above both valuations earns `0`,
more than `2 max = −2`. Only the bound needs it; the two profit values hold without it. -/
theorem transparent_benchmark (P : Params) :
    (0 ≤ max (P.vH - P.cH) (P.vL - P.cL) → ∀ (m1 m2 : Product) (p1 p2 : ℝ),
      transparentProfit P m1 m2 p1 p2 ≤ 2 * max (P.vH - P.cH) (P.vL - P.cL)) ∧
    (P.vL - P.cL ≤ P.vH - P.cH →
      transparentProfit P .H .H P.vH P.vH = 2 * (P.vH - P.cH)) ∧
    (P.vH - P.cH ≤ P.vL - P.cL →
      transparentProfit P .L .L P.vL P.vL = 2 * (P.vL - P.cL)) := by sorry

end HuangYin
