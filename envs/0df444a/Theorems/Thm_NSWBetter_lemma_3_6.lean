-- Prove2me | Theorems.Thm_NSWBetter_lemma_3_6
-- name    : NSWBetter.lemma_3_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:55:51.065997+00:00
-- url     : https://prove2.me/theorems/cf7d4bbc-8c71-43cf-b189-cd9c75400972
-- title:
--   Lemma 3.6 — upper bound on $\mathrm{NSW}(I)$ through large goods and the mean value
-- statement:
--   Let $I$ be an instance with $\Delta\ge1$ agents sharing the valuation $v\ge0$, with set of large goods $L$, $\ell=|L|$, and mean value $\mu$. Then
--   $$\mathrm{NSW}(I)\le\Bigl(\frac{\Delta\mu}{\Delta-\ell}\Bigr)^{1-\ell/\Delta}\Bigl(\prod_{g\in L}v(g)\Bigr)^{1/\Delta},$$
--   and, with $\ln0=-\infty$,
--   $$\mathrm{logNSW}(I)\le\frac1\Delta\Bigl[\sum_{g\in L}\ln v(g)+(\Delta-\ell)\ln\frac{\Delta\mu}{\Delta-\ell}\Bigr]\le\frac1\Delta\Bigl[\sum_{g\in L}\ln v(g)+(\Delta-\ell)\ln\mu\Bigr]+\frac1e .$$
--
--   This is the upper bound against which the round robin allocation is compared in Section 3.
--
--   Differences from the source:
--   - encoding: identical valuation $v:2^G\to\mathbb R_{\ge0}$ with $\Delta$ agents → `v : Fin m → ℝ`, $v\ge0$, $\Delta\ge1$; reason: Lean convention; an instance has at least one agent; same instances
--   - encoding: $\mathrm{logNSW}(I)$ and the logarithms, with $\ln0=-\infty$ → `EReal` values via `HayashiHoeffding.elog`; reason: Lean's `Real.log 0 = 0` would change the inequalities when a value is $0$; same values whenever the logs are finite
-- source:
--   Viswanathan, A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations, arXiv:2607.13340 (held version, sha256 08811cb468c2df39231dca4222c5af94163587c7c83e205e50bbf0b91fc1deb3), Lemma 3.6, p.12

import Mathlib
import Definitions.Def_HayashiHoeffding_elog
import Definitions.Def_NSWBetter_largeCount
import Definitions.Def_NSWBetter_meanVal
import Definitions.Def_NSWBetter_vals
import Definitions.Def_NSWBetter_largeGoods
import Definitions.Def_NSWBetter_nswOpt

namespace NSWBetter

/-- **Lemma 3.6 — upper bound on the optimal Nash welfare.**
Viswanathan, *A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations*, arXiv:2607.13340 (held version, sha256 08811cb4…), Lemma 3.6, p.12: "Let I be an instance where all agents have the same valuation function v. Then, NSW(I) ≤ (∆µ/(∆−ℓ))^(1−ℓ/∆) (Π_(g∈L) v(g))^(1/∆). Alternatively, logNSW(I) ≤ (1/∆)[Σ_(g∈L) ln v(g) + (∆−ℓ) ln(∆µ/(∆−ℓ))] ≤ (1/∆)[Σ_(g∈L) ln v(g) + (∆−ℓ) ln µ] + 1/e."

All three inequalities, for every instance with `Δ ≥ 1` identical agents and nonnegative values.

**Formalization Note.** The log forms are in `EReal` with `ln 0 = −∞` (`HayashiHoeffding.elog`), so they need no positivity hypothesis; under Assumption 3.5 every term is finite. -/
theorem lemma_3_6 (Δ m : ℕ) (hΔ : 1 ≤ Δ) (v : Fin m → ℝ) (hv : ∀ g, 0 ≤ v g) :
    nswOpt Δ (vals v) ≤
        ((Δ : ℝ) * meanVal Δ (vals v) / ((Δ : ℝ) - largeCount Δ (vals v))) ^
            (1 - (largeCount Δ (vals v) : ℝ) / Δ) *
          (∏ g ∈ largeGoods Δ v, v g) ^ ((1 : ℝ) / Δ) ∧
      HayashiHoeffding.elog (nswOpt Δ (vals v)) ≤
        ((1 / Δ : ℝ) : EReal) * (∑ g ∈ largeGoods Δ v, HayashiHoeffding.elog (v g) +
          (((Δ : ℝ) - largeCount Δ (vals v) : ℝ) : EReal) *
            HayashiHoeffding.elog ((Δ : ℝ) * meanVal Δ (vals v) / ((Δ : ℝ) - largeCount Δ (vals v)))) ∧
      ((1 / Δ : ℝ) : EReal) * (∑ g ∈ largeGoods Δ v, HayashiHoeffding.elog (v g) +
          (((Δ : ℝ) - largeCount Δ (vals v) : ℝ) : EReal) *
            HayashiHoeffding.elog ((Δ : ℝ) * meanVal Δ (vals v) / ((Δ : ℝ) - largeCount Δ (vals v)))) ≤
        ((1 / Δ : ℝ) : EReal) * (∑ g ∈ largeGoods Δ v, HayashiHoeffding.elog (v g) +
          (((Δ : ℝ) - largeCount Δ (vals v) : ℝ) : EReal) * HayashiHoeffding.elog (meanVal Δ (vals v))) +
          ((1 / Real.exp 1 : ℝ) : EReal) := by sorry

end NSWBetter
