-- Prove2me | Theorems.Thm_MNLTrisection_Adaptive_Supplement_theorem_2
-- name    : MNLTrisection.Adaptive.Supplement.theorem_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T22:14:28.318857+00:00
-- url     : https://prove2.me/theorems/66560440-44cc-4a92-8705-405bbdbe6534
-- title:
--   Theorem 2 (corrected: T ≥ 2) — baseline trisection regret
-- statement:
--   There is a positive absolute constant $C$, chosen before the product count, horizon and all model parameters, such that for every $N$, every integer $T\ge2$, nonnegative utilities $v_i$, and known revenues $r_i\in[0,1]$, the baseline Algorithm 1 has expected regret
--
--   $$\operatorname{Reg}_{\pi_{\mathrm{base}}}(T;v,r)\le C\sqrt{T\ln T}.$$
--
--   The optimum is over all assortments. This is the companion baseline guarantee, with its own policy and confidence schedule, rather than the published adaptive-confidence goal. A final partial epoch is included in the $T$ offers.
--
--   **Formalization Note** The policy uses the algorithm box's exact count $16\lceil\epsilon^{-2}\ln T\rceil$ and confidence radius $\sqrt{\ln(T^2)/(2t)}$. The conflicting prose and Supplement B counts are retained in the audit. No completion-of-epoch premise is imposed.
--
--   Differences from the source:
--   - correction: an unrestricted horizon, with the printed loop count zero at T=1 → T≥2; reason: Algorithm 1 p.9 cannot serve any customer at T=1; the positive-horizon boundary is disclosed and excluded, rather than claiming a zero regret bound after a totalization
--   - reading: line 6 has 16⌈ε⁻² ln T⌉, while p.10 and Supplement B use ln(T²) and disagree on ceiling placement → the exact algorithm-box count 16⌈ε⁻² ln T⌉; reason: the policy being asserted is Algorithm 1; all source anchors are preserved, and this count still gives the stated rate
--   - reading: §3 initially requires positive revenues, while Theorem 2 states r_i∈[0,1] → nonnegative revenues, including zero, as the theorem states; reason: zero revenues are explicitly allowed in the theorem and all operations remain defined
--   - reading: §3 excludes the empty set, but defines the assortment family as all subsets → all subsets, including the empty assortment; reason: the published base model uses all subsets, and Algorithm 1 may produce an empty level set; empty offers give no purchase and zero revenue
--   - encoding: products 1,…,N, periods 1,…,T, outside choice 0 → Fin N, Fin T and Option (Fin N), with none for no purchase; reason: bijective indexing; the same MNL law, revenues and all zero-utility dummy items are retained
-- source:
--   Chen, Wang & Zhou, An Optimal Policy for Dynamic Assortment Planning Under Uncapacitated Multinomial Logit Models, arXiv:1805.04785v2, PDF p.10, Theorem 2, Eq.(7); Algorithms 1–2, PDF p.9; proof PDF p.11 and Supplement B, PDF pp.22–23

import Mathlib
import Definitions.Def_MNLTrisection_Adaptive_Supplement_Baseline

namespace MNLTrisection.Adaptive.Supplement

/-- Theorem 2, PDF p.10 (corrected horizon T ≥ 2). C is absolute,
chosen before dimensions, horizons and all model parameters. -/
theorem theorem_2 :
    ∃ C : ℝ, 0 < C ∧ ∀ (N T : ℕ), 2 ≤ T →
      ∀ (v r : Fin N → ℝ), (∀ i, 0 ≤ v i) → (∀ i, r i ∈ Set.Icc 0 1) →
        MNLBandit.UCB.regret v r Finset.univ ⟨∅, Finset.mem_univ _⟩
          (baselinePolicy r T) T ≤ C * Real.sqrt ((T : ℝ) * Real.log T) := by sorry

end MNLTrisection.Adaptive.Supplement
