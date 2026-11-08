-- Prove2me | Theorems.Thm_LearnVsOpt_lemma_6_1
-- name    : LearnVsOpt.lemma_6_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:08:10.413205+00:00
-- url     : https://prove2.me/theorems/85c646ae-ef22-4fa8-8457-6e04e6bdf385
-- title:
--   Lemma 6.1, p.16 — the forecast has drift at most 1
-- statement:
--   In every active round $t$ of the algorithm, on every outcome and against any adaptive optimizer, the forecast distribution $F_t$ returned by Algorithm 2 satisfies
--   $$
--   \mathbb E_{f\sim F_t}\big[\langle Z_{t-1},\delta(f,k)\rangle\big]\le1\qquad\text{for all } k\in[\hat n_{t-1}].
--   $$
--   So simulating gradient ascent gives an approximate equilibrium of the zero-sum game between the forecaster and the environment, against every outcome observed so far.
--
--   Differences from the source:
--   - encoding: T rounds; rounds t = 1, …, T; actions [n_O], [n_L]; forecasts in Δ_{n̂}; the iterates of F_t; expectations → T ≥ 1, Outcome lists with round t at position t − 1, actions Fin nO, Fin nL, forecasts ℕ → ℝ vanishing past the dictionary, F_t as the list of M_t iterates, expect as a finite-support tsum; reason: Lean representation of the same objects
--   - encoding: R_t, L_t, Z_t as sums of expected errors → read from the state of the program of Algorithms 1 and 2: atoms (k, j₁, j₂, w, q) for R_t and 2√n_L·L_t for L_t; reason: the program stores the same sums; the theorems speak about the program's own Z_t
--   - encoding: δ(f, k), k an index of 𝒰𝒞 → δ(f, v), v = uc^(k) the realized vector; the indicator 1_{k=k'} reads D[k'] = v; reason: same object for a dictionary without repeats; also defined for a vector not yet observed
--   - encoding: each player has a null action of cost 0 (§2, p.6), with the all-zeros vector uc^(1) = 0 ∈ 𝒰𝒞 (p.16) → j₀ with C_L[i, j₀] = 0 for all i, and hzero: some row i has U_L[i, ·] = C_L[i, ·] = 0; reason: the paper's standing assumptions, as hypotheses
--   - reading: Algorithm 1 indents "Observe … report it to the forecaster" under the active branch (p.7) → the dictionary is updated in every round, and Z_t only in active rounds; reason: §2, p.6 assumes full-information feedback, p.16 defines 𝒰𝒞_t by the vectors observed in rounds 1, …, t, and the proofs of Claim 6.6 and Lemma 6.2 need exactly this
--   - generalization: an adaptive optimizer whose i_t is chosen against the learner → a kernel σ from the full past (i_r, m_r, j_r), r < t, including the learner's realized forecast indices, to PMF (Fin n_O); reason: every optimizer that sees less is an instance; moves within a round stay simultaneous
--   - generalization: any consistent tie-breaking rule, with J⃗ = (j, j) and Q = 0 for a pure best response (p.8) → every selector valid on (u, c) ∈ [0, 1]^{2n_L} with c[j₀] = 0; the only condition on J⃗ is j₁ = j₂ → Q = 0, so a pair j₁ ≠ j₂ with Q ∈ {0, 1} is also allowed; reason: the paper's rule is a valid selector, and its arguments use no more than validity
--   - generalization: ρ_L ∈ (0, 1] with ρ_L = Ω(1) w.r.t. T (§2, p.6) → any ρ_L ∈ (0, 1], with no relation to T; reason: the bounds are explicit in ρ_L; a constant ρ_L is an instance
--   - reading: in every active round, against any optimizer, with no expectation over the path → the inequality for every outcome in the support; reason: the paper's proof holds on every path
-- source:
--   Fikioris, Sivan & Tardos, Learning vs. Optimizing Players in Budgeted Games, arXiv:2611.05580, Lemma 6.1, (19), p.16

import Mathlib
import Definitions.Def_LearnVsOpt_Play

open scoped Matrix

namespace LearnVsOpt

/-- **Lemma 6.1** (Fikioris, Sivan & Tardos, arXiv:2611.05580, Lemma 6.1, (19), p.16). In every active
round `t`, the forecast distribution `F_t` returned by Algorithm 2 satisfies
`E_{f∼F_t}[⟨Z_{t−1}, δ(f, k)⟩] ≤ 1` for all `k ∈ [n̂_{t−1}]`. -/
theorem lemma_6_1 {nO nL : ℕ} (G : Game nO nL) (ρL : ℝ) (hρ₀ : 0 < ρL) (hρ₁ : ρL ≤ 1)
    (j₀ : Fin nL) (hj₀ : ∀ i, G.CL i j₀ = 0) (hzero : ∃ i, ∀ j, G.UL i j = 0 ∧ G.CL i j = 0)
    (T : ℕ) (hT : 1 ≤ T) (sel : Selector nL) (hsel : IsValidSel j₀ ρL sel) (σ : Optimizer nO nL)
    {ω : Outcome nO nL} (hω : ω ∈ (law G σ ⟨T, ρL, j₀, sel⟩).support)
    (t : ℕ) (ht : t ∈ Finset.Icc 1 T) (hact : ω.IsActive t)
    (k : ℕ) (hk : k < (ω.stAt (t - 1)).dict.length) :
    ω.drift ρL t ((ω.stAt (t - 1)).dict.getD k 0) ≤ 1 := by sorry

end LearnVsOpt
