-- Prove2me | Theorems.Thm_NSWBetter_theorem_3_15
-- name    : NSWBetter.theorem_3_15
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:53:06.876205+00:00
-- url     : https://prove2.me/theorems/e1bb70c4-9cb9-48a3-b8d5-a2214e5521c8
-- title:
--   Theorem 3.15 — removing at most half of each value class outside the top $\Delta$ goods
-- statement:
--   Let $I$ be an instance with $\Delta\ge1$ identical agents and nonnegative values satisfying Assumption 3.5. Partition the goods into classes $G_1,\dots,G_{k'}$ of equal value, let $G^\Delta$ be a set of $\Delta$ goods each weakly more valuable than every good outside it, and remove a set $R$ of goods with
--   $$|R\cap G_k|\le\tfrac12|G_k\setminus G^\Delta|\quad\text{for every class }k .$$
--   Then the round robin allocation $W^{mod}$ of the remaining instance satisfies
--   $$\mathrm{logNSW}(W^{mod})\ge\mathrm{logNSW}(I)-\frac1e-2 .$$
--
--   Differences from the source:
--   - encoding: identical valuation with $\Delta$ agents → `v : Fin m → ℝ`, $v\ge0$, $\Delta\ge1$; reason: Lean convention; same instances
--   - encoding: $\mathrm{logNSW}(W^{mod})$ with $\ln0=-\infty$ → `EReal` via `HayashiHoeffding.elog`; reason: same values whenever finite
--   - encoding: $\mathrm{logNSW}(I)$ → `Real.log` of the maximum over full assignments; reason: positive under Assumption 3.5; same maximum for nonnegative values
--   - encoding: a partition into classes $G_1,\dots,G_{k'}$ of equal value → a labelling `cls : Fin m → ℕ` with equal values on equal labels; reason: every such partition is a labelling and conversely; same instances
-- source:
--   Viswanathan, A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations, arXiv:2607.13340 (held version, sha256 08811cb468c2df39231dca4222c5af94163587c7c83e205e50bbf0b91fc1deb3), Theorem 3.15, p.15

import Mathlib
import Definitions.Def_NSWBetter_vals
import Definitions.Def_NSWBetter_Asm35
import Definitions.Def_NSWBetter_logNSWrr
import Definitions.Def_NSWBetter_nswOpt

namespace NSWBetter

/-- **Theorem 3.15.**
Viswanathan, *A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations*, arXiv:2607.13340 (held version, sha256 08811cb4…), Theorem 3.15, p.15: "Let I be an instance with ∆ identical agents that satisfies Assumption 3.5. Partition the goods into classes G1, G2, . . . , Gk′ such that all goods in each class have the same value. Let G∆ be a set of ∆ goods in the instance such that each good in G∆ is weakly more valuable than each of the goods outside G∆. Let Imod be the instance I after removing a set R of goods, such that |R ∩ Gk| ≤ (1/2)|Gk \ G∆| for each k ∈ [k′]. Let Wmod be the round robin allocation in the instance Imod. The following holds: logNSW(Wmod) ≥ logNSW(I) − 1/e − 2."

**Formalization Note.** The partition is given by a labelling `cls` of the goods, constant value on each label; every partition into equal-value classes is of this form. -/
theorem theorem_3_15 (Δ m : ℕ) (hΔ : 1 ≤ Δ) (v : Fin m → ℝ) (hv : ∀ g, 0 ≤ v g)
    (h35 : Asm35 Δ (vals v)) (cls : Fin m → ℕ) (hcls : ∀ g g', cls g = cls g' → v g = v g')
    (GΔ : Finset (Fin m)) (hGcard : GΔ.card = Δ) (hGtop : ∀ g ∈ GΔ, ∀ g' ∉ GΔ, v g' ≤ v g)
    (R : Finset (Fin m))
    (hR : ∀ k : ℕ, 2 * (R.filter fun g => cls g = k).card ≤
      ((Finset.univ.filter fun g => cls g = k) \ GΔ).card) :
    ((Real.log (nswOpt Δ (vals v)) - 1 / Real.exp 1 - 2 : ℝ) : EReal) ≤
      logNSWrr Δ ((Finset.univ \ R).val.map v) := by sorry

end NSWBetter
