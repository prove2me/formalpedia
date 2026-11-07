-- Prove2me | Theorems.Thm_NSWBetter_theorem_3_9
-- name    : NSWBetter.theorem_3_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:55:56.467092+00:00
-- url     : https://prove2.me/theorems/74cca607-d9d6-4e5e-9ca8-a3ef94dd98c4
-- title:
--   Theorem 3.9 — round robin beats $e^{1/e}$ on non-well-behaved instances
-- statement:
--   There is an absolute constant $c>0$ such that for every instance $I$ with $\Delta\ge1$ identical agents and nonnegative values that satisfies Assumption 3.5 and is **not** well-behaved, the round robin allocation $W$ satisfies
--   $$\mathrm{logNSW}(W)\ge\mathrm{logNSW}(I)-\frac1e+c .$$
--
--   With Fact 2.2 this says that $W$ is strictly better than an $e^{1/e}$-approximation outside the well-behaved structure.
--
--   Differences from the source:
--   - reading: "for some constant $c>0$" → one $c$ for all instances ($\exists c$ before $\forall\Delta,m,v$); reason: the constant is applied uniformly in Lemma 4.17 and Theorem 4.21; a per-instance constant would be weaker
--   - encoding: identical valuation with $\Delta$ agents → `v : Fin m → ℝ`, $v\ge0$, $\Delta\ge1$; reason: Lean convention; same instances
--   - encoding: $\mathrm{logNSW}(W)$ with $\ln0=-\infty$ → `EReal` via `HayashiHoeffding.elog`; reason: same values whenever finite
--   - encoding: $\mathrm{logNSW}(I)$ → `Real.log` of the maximum over full assignments; reason: positive under Assumption 3.5; for nonnegative values full assignments give the same maximum
-- source:
--   Viswanathan, A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations, arXiv:2607.13340 (held version, sha256 08811cb468c2df39231dca4222c5af94163587c7c83e205e50bbf0b91fc1deb3), Theorem 3.9, p.13

import Mathlib
import Definitions.Def_NSWBetter_vals
import Definitions.Def_NSWBetter_Asm35
import Definitions.Def_NSWBetter_logNSWrr
import Definitions.Def_NSWBetter_WellBehaved
import Definitions.Def_NSWBetter_nswOpt

namespace NSWBetter

/-- **Theorem 3.9 — non-well-behaved instances.**
Viswanathan, *A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations*, arXiv:2607.13340 (held version, sha256 08811cb4…), Theorem 3.9, p.13: "Let I be an instance with ∆ identical agents that satisfies Assumption 3.5. Define W as the round robin allocation of this instance. If I is not a well-behaved instance, then for some constant c > 0, logNSW(W) ≥ logNSW(I) − 1/e + c."

**Formalization Note.** The constant `c` is one absolute constant, chosen before the instance. `logNSW(I) = ln NSW(I)` is finite under Assumption 3.5; `logNSW(W)` is in `EReal`. -/
theorem theorem_3_9 :
    ∃ c : ℝ, 0 < c ∧ ∀ (Δ m : ℕ) (v : Fin m → ℝ), 1 ≤ Δ → (∀ g, 0 ≤ v g) →
      Asm35 Δ (vals v) → ¬ WellBehaved Δ (vals v) →
      ((Real.log (nswOpt Δ (vals v)) - 1 / Real.exp 1 + c : ℝ) : EReal) ≤ logNSWrr Δ (vals v) := by sorry

end NSWBetter
