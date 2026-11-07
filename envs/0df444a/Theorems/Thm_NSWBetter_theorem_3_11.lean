-- Prove2me | Theorems.Thm_NSWBetter_theorem_3_11
-- name    : NSWBetter.theorem_3_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:56:15.564205+00:00
-- url     : https://prove2.me/theorems/d6c8eb4a-0630-4e3b-b08e-2ba2f59909a6
-- title:
--   Theorem 3.11 — removing small goods and adding large goods
-- statement:
--   Let $I$ be a well-behaved instance with $\Delta\ge1$ identical agents and nonnegative values satisfying Assumption 3.5, with large goods $L$ and mean value $\mu$. Remove a set $R$ of small goods and add a multiset $A$ of new goods, each of value at least $\mu/\gamma$, with $|A|\le0.01\Delta$ and $v(R)\le0.1\Delta\mu$. If $W^{mod}$ is the round robin allocation of the modified instance, then
--   $$\mathrm{logNSW}(W^{mod})\ge\mathrm{logNSW}(I)-\frac1e+\frac1\Delta\bigl(10|A|-2|R|\bigr).$$
--
--   Differences from the source:
--   - encoding: identical valuation with $\Delta$ agents → `v : Fin m → ℝ`, $v\ge0$, $\Delta\ge1$; reason: Lean convention; same instances
--   - encoding: $\mathrm{logNSW}(W^{mod})$ with $\ln0=-\infty$ → `EReal` via `HayashiHoeffding.elog`; reason: same values whenever finite
--   - encoding: $\mathrm{logNSW}(I)$ → `Real.log` of the maximum over full assignments; reason: positive under Assumption 3.5; same maximum for nonnegative values
--   - encoding: the added goods $A$ and the modified instance → the multiset of values of $A$, and $I^{mod}$ as the value multiset of $G\setminus R$ plus $A$; reason: round robin depends only on the values; same instances
-- source:
--   Viswanathan, A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations, arXiv:2607.13340 (held version, sha256 08811cb468c2df39231dca4222c5af94163587c7c83e205e50bbf0b91fc1deb3), Theorem 3.11, p.14

import Mathlib
import Definitions.Def_NSWBetter_gamma
import Definitions.Def_NSWBetter_meanVal
import Definitions.Def_NSWBetter_vals
import Definitions.Def_NSWBetter_largeGoods
import Definitions.Def_NSWBetter_Asm35
import Definitions.Def_NSWBetter_logNSWrr
import Definitions.Def_NSWBetter_WellBehaved
import Definitions.Def_NSWBetter_nswOpt

namespace NSWBetter

/-- **Theorem 3.11.**
Viswanathan, *A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations*, arXiv:2607.13340 (held version, sha256 08811cb4…), Theorem 3.11, p.14: "Let I be a well-behaved instance that satisfies Assumption 3.5 with ∆ identical agents, a set of large goods L and mean value µ. Let W denote the round robin allocation of this instance. Let Imod be the instance I after removing a set of small goods R and adding a set of large goods A; let Wmod be the round robin allocation in this modified instance. If each good in A has value at least µ/γ, |A| ≤ 0.01∆ and v(R) ≤ 0.1∆µ, then logNSW(Wmod) ≥ logNSW(I) − 1/e + (1/∆)(10|A| − 2|R|)."

**Formalization Note.** `R` is a set of small goods of `I`; the added goods `A` are given by the multiset of their values. No assumption is made on `Imod` (Section 3.1, p.14). -/
theorem theorem_3_11 (Δ m : ℕ) (hΔ : 1 ≤ Δ) (v : Fin m → ℝ) (hv : ∀ g, 0 ≤ v g)
    (h35 : Asm35 Δ (vals v)) (hwb : WellBehaved Δ (vals v))
    (R : Finset (Fin m)) (hR : ∀ g ∈ R, g ∉ largeGoods Δ v) (A : Multiset ℝ)
    (hA : ∀ a ∈ A, meanVal Δ (vals v) / gamma ≤ a) (hAcard : (A.card : ℝ) ≤ 0.01 * Δ)
    (hRval : ∑ g ∈ R, v g ≤ 0.1 * Δ * meanVal Δ (vals v)) :
    ((Real.log (nswOpt Δ (vals v)) - 1 / Real.exp 1 +
        (1 / Δ : ℝ) * (10 * (A.card : ℝ) - 2 * (R.card : ℝ)) : ℝ) : EReal) ≤
      logNSWrr Δ ((Finset.univ \ R).val.map v + A) := by sorry

end NSWBetter
