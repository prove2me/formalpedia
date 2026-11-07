-- Prove2me | Theorems.Thm_NSWBetter_theorem_3_10
-- name    : NSWBetter.theorem_3_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:56:15.191205+00:00
-- url     : https://prove2.me/theorems/16f557ef-f217-4f2e-b583-6bae5398230a
-- title:
--   Theorem 3.10 — round robin is an $e^{1/e}$-approximation of the Lemma 3.6 bound
-- statement:
--   For every instance with $\Delta\ge1$ identical agents and nonnegative values satisfying Assumption 3.5, with large goods $L$, $\ell=|L|$, mean value $\mu$ and round robin allocation $W$,
--   $$\mathrm{logNSW}(W)\ge\frac1\Delta\Bigl[\sum_{g\in L}\ln v(g)+(\Delta-\ell)\ln\frac{\Delta\mu}{\Delta-\ell}\Bigr]-\frac1e .$$
--
--   The bracket is the upper bound of Lemma 3.6, so $W$ is an $e^{1/e}$-approximation of that bound.
--
--   Differences from the source:
--   - encoding: identical valuation with $\Delta$ agents → `v : Fin m → ℝ`, $v\ge0$, $\Delta\ge1$; reason: Lean convention; same instances
--   - encoding: $\mathrm{logNSW}(W)$ with $\ln0=-\infty$ → `EReal` via `HayashiHoeffding.elog`; reason: same values whenever finite
-- source:
--   Viswanathan, A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations, arXiv:2607.13340 (held version, sha256 08811cb468c2df39231dca4222c5af94163587c7c83e205e50bbf0b91fc1deb3), Theorem 3.10, p.13

import Mathlib
import Definitions.Def_NSWBetter_largeCount
import Definitions.Def_NSWBetter_meanVal
import Definitions.Def_NSWBetter_vals
import Definitions.Def_NSWBetter_largeGoods
import Definitions.Def_NSWBetter_Asm35
import Definitions.Def_NSWBetter_logNSWrr

namespace NSWBetter

/-- **Theorem 3.10.**
Viswanathan, *A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations*, arXiv:2607.13340 (held version, sha256 08811cb4…), Theorem 3.10, p.13: "Let I be an instance with ∆ identical agents that satisfies Assumption 3.5. Define W as the round robin allocation. The following holds, logNSW(W) ≥ (1/∆)[Σ_(g∈L) ln v(g) + (∆−ℓ) ln(∆µ/(∆−ℓ))] − 1/e."

**Formalization Note.** Under Assumption 3.5, `µ > 0` and every large good has value `> ∆µ/(∆−ℓ) > 0`, so the logarithms on the right are of positive numbers. -/
theorem theorem_3_10 (Δ m : ℕ) (hΔ : 1 ≤ Δ) (v : Fin m → ℝ) (hv : ∀ g, 0 ≤ v g)
    (h35 : Asm35 Δ (vals v)) :
    (((1 / Δ : ℝ) * (∑ g ∈ largeGoods Δ v, Real.log (v g) +
        ((Δ : ℝ) - largeCount Δ (vals v)) *
          Real.log ((Δ : ℝ) * meanVal Δ (vals v) / ((Δ : ℝ) - largeCount Δ (vals v)))) -
        1 / Real.exp 1 : ℝ) : EReal) ≤ logNSWrr Δ (vals v) := by sorry

end NSWBetter
