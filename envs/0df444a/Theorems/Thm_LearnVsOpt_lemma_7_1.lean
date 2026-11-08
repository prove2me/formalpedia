-- Prove2me | Theorems.Thm_LearnVsOpt_lemma_7_1
-- name    : LearnVsOpt.lemma_7_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:03:56.902203+00:00
-- url     : https://prove2.me/theorems/3e4db5f4-ae22-47eb-94c6-e45804301865
-- title:
--   Lemma 7.1, p.23 — $\mathrm{BSE}=\min_{\mu\ge0}\mathrm{BSE}_\mu$, with $\mu^\star\le1/\rho_O$
-- statement:
--   Let the learner and the optimizer each have an action of zero cost, and let $\rho_L,\rho_O\in(0,1]$. The two-phase value (26) and the Lagrangian values (27) satisfy
--   $$
--   \mathrm{BSE}_2=\min_{\mu\ge0}\mathrm{BSE}_\mu ,
--   $$
--   with the minimum attained, and every minimizer satisfies $\mu^\star\le1/\rho_O$.
--
--   This allows a budgeted optimizer to be replaced by an unbudgeted one with rewards of range $O(1/\rho_O)$.
--
--   Differences from the source:
--   - encoding: max in (2), (26), (27); both (2) and (26) are named BSE → sSup of the set of values, named BSE and BSE₂; reason: the sets are nonempty and bounded under the null actions; attainment is not a claim of the theorem
--   - encoding: the null actions of §2 and §7 → j₀ with C_L[i, j₀] = 0, and ∃ i, C_O[i, ·] = 0; reason: the paper's assumptions, as hypotheses
--   - encoding: BSE = min_{μ≥0} BSE_μ → ∃ μ⋆ ≥ 0 with BSE₂ = BSE_{μ⋆}, and BSE₂ ≤ BSE_μ for every μ ≥ 0; reason: the meaning of an attained minimum
--   - reading: "for the optimal value it holds μ⋆ ≤ 1/ρ_O" → every μ ≥ 0 with BSE_μ = BSE₂ satisfies μ ≤ 1/ρ_O; reason: the proof says "any minimizer"
-- source:
--   Fikioris, Sivan & Tardos, Learning vs. Optimizing Players in Budgeted Games, arXiv:2611.05580, Lemma 7.1, p.23

import Mathlib
import Definitions.Def_LearnVsOpt_BSE

namespace LearnVsOpt

/-- **Lemma 7.1** (Fikioris, Sivan & Tardos, arXiv:2611.05580, Lemma 7.1, p.23). `BSE = min_{μ≥0} BSE_μ`
for the two-phase value (26) and the Lagrangian value (27), with the minimum attained, and every
minimizer satisfies `μ⋆ ≤ 1/ρ_O`. -/
theorem lemma_7_1 {nO nL : ℕ} (G : Game nO nL) (ρL ρO : ℝ) (hρL₀ : 0 < ρL) (hρL₁ : ρL ≤ 1)
    (hρO₀ : 0 < ρO) (hρO₁ : ρO ≤ 1) (j₀ : Fin nL) (hj₀ : ∀ i, G.CL i j₀ = 0)
    (hnull : ∃ i, ∀ j, G.CO i j = 0) :
    (∃ μS : ℝ, 0 ≤ μS ∧ G.BSE₂ ρL ρO = G.BSEmu ρL ρO μS) ∧
    (∀ μ : ℝ, 0 ≤ μ → G.BSE₂ ρL ρO ≤ G.BSEmu ρL ρO μ) ∧
    ∀ μ : ℝ, 0 ≤ μ → G.BSEmu ρL ρO μ = G.BSE₂ ρL ρO → μ ≤ 1 / ρO := by sorry

end LearnVsOpt
