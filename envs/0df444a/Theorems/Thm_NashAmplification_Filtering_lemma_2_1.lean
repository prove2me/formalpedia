-- Prove2me | Theorems.Thm_NashAmplification_Filtering_lemma_2_1
-- name    : NashAmplification.Filtering.lemma_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:19:08.484302+00:00
-- url     : https://prove2.me/theorems/c8ef39ec-7db4-4d5e-8743-e41ed68abc72
-- title:
--   Lemma 2.1 — score criterion
-- statement:
--   Let $k\ge2$, let every action set $A_r$ be finite and nonempty, and let $G$ have payoffs in $[0,1]$. Let $Q$ be any probability distribution on $A=\prod_r A_r$, possibly correlated, and let $x$ be its marginals played independently. For any $\beta,\Delta>0$, if
--   $$Q\{a:V_Q^*-V_Q(a)\le\Delta\}\ge1-\beta,$$
--   then $x$ is a $(\beta+k\Delta)$-approximate Nash equilibrium of $G$. The score is defined on all tuples, not merely the support of $Q$.
--
--   The criterion connects the recovery test to approximate equilibrium in the input game.
--
--   Differences from the source:
--   - encoding: finite nonempty action sets and one-based player indices → positive action counts with Fin indices, mixed-radix table order, and zero-based coordinates; reason: finite relabeling preserves every source game and distribution
--   - encoding: pure unilateral deviations and a maximum gain bound → all mixed unilateral deviations in IsEpsApproxNash; reason: the proved mixed_deviation and ane_iff equivalences recover exactly (2.1)
-- source:
--   Deng, Li, Wang and Zhang, Hardness Amplification for Approximate Nash Equilibrium with a Constant Number of Players, STOC 2027 submission #120 (October 2026), SHA-256 c201a27da9b9920a924945f1a30c7919ae6b922c99430223ee9bbcdec5b0ffa8, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/120.pdf, Lemma 2.1, PDF p. 7 (printed p. 6)

import Definitions.Def_NashAmplification_Filtering_Model

open scoped BigOperators
noncomputable section

namespace NashAmplification.Filtering

/-- Lemma 2.1, PDF 7 (printed 6), criterion (2.4). -/
theorem lemma_2_1 {k : ℕ} (hk : 2 ≤ k) {n : Fin k → ℕ}
    (hn : ∀ r, 0 < n r) (u : Utility n) (hu : BoundedGame u)
    (Q : Tuple n → ℝ) (hQ : AGT.IsLottery Q)
    (β Δ : ℝ) (hβ : 0 < β) (hΔ : 0 < Δ)
    (hpass : 1 - β ≤ scoreMass u Q Δ) :
    DGPNash.WellSupported.IsEpsApproxNash u (marginal Q) (β + k * Δ) := by sorry
end NashAmplification.Filtering
