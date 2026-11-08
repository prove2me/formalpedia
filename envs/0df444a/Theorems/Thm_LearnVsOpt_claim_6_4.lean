-- Prove2me | Theorems.Thm_LearnVsOpt_claim_6_4
-- name    : LearnVsOpt.claim_6_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:08:24.066954+00:00
-- url     : https://prove2.me/theorems/9e7e6c02-2839-425f-b570-d5df34fa7674
-- title:
--   Claim 6.4, p.19 — first term of (22): a martingale
-- statement:
--   Suppose $[T]$ is partitioned into $S\ge1$ contiguous intervals $I_s$, and in each $I_s$ the optimizer draws $i_t\sim x^{(s)}$ independently. With $s$ the interval containing $\tau$ and $f^{\star(s)}$ the law of the realized index under $x^{(s)}$,
--   $$
--   \mathbb E\Big[\max_{t\le T}\sum_{\tau\in\mathcal T_t}\Big\langle Z_{\tau-1},\bar\delta_\tau(k_\tau)-\sum_k f_k^{\star(s)}\bar\delta_\tau(k)\Big\rangle\Big]\le2\sqrt{5T}\,\sqrt{\mathbb E\big[\max_{t\le T}\|Z_t\|^2\big]}.
--   $$
--   This is the first of the three terms in the proof of Lemma 6.3.
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
--   - encoding: [T] partitioned into S ≥ 1 contiguous intervals I_s with i_t ∼ x^(s) in each → IsPiecewiseStationary: I s = Ioc a b, pairwise disjoint, with union Icc 1 T; (σ past i).toReal = x s i for all pasts of length t − 1, t ∈ I s; empty intervals allowed; reason: same objects; an empty interval carries no constraint
--   - encoding: ⟨Z_{t−1}, δ̄_t(k)⟩, Σ_k f^⋆_k δ̄_t(k), Σ_k f̂_k δ̄_t(k) → E_{f∼F_t}⟨Z_{t−1}, δ(f, v)⟩ over v; the law f^⋆ as Σ_i x_i over the optimizer's actions; f̂ as the average over the earlier rounds of the interval, and the zero vector in the interval's first round; reason: linearity of the inner product, and the paper's indexing of 𝒰𝒞 by first observation is path dependent
--   - encoding: max_{t≤T} → sup' over t ∈ {1, …, T}, T ≥ 1; reason: the set is nonempty
-- source:
--   Fikioris, Sivan & Tardos, Learning vs. Optimizing Players in Budgeted Games, arXiv:2611.05580, Claim 6.4, p.19

import Mathlib
import Definitions.Def_LearnVsOpt_Play

open scoped Matrix

namespace LearnVsOpt

open Classical in
/-- **Claim 6.4** (Fikioris, Sivan & Tardos, arXiv:2611.05580, Claim 6.4, p.19). Under the hypotheses
of Lemma 6.3, for the first term of (22),
`E[max_{t≤T} Σ_{τ∈𝒯_t} ⟨Z_{τ−1}, δ̄_τ(k_τ) − Σ_k f^{⋆(s)}_k δ̄_τ(k)⟩] ≤ 2√(5T) √(E[max_{t≤T} ‖Z_t‖²])`,
with `s` the interval containing `τ`. -/
theorem claim_6_4 {nO nL : ℕ} (G : Game nO nL) (ρL : ℝ) (hρ₀ : 0 < ρL) (hρ₁ : ρL ≤ 1)
    (j₀ : Fin nL) (hj₀ : ∀ i, G.CL i j₀ = 0) (hzero : ∃ i, ∀ j, G.UL i j = 0 ∧ G.CL i j = 0)
    (T : ℕ) (hT : 1 ≤ T) (sel : Selector nL) (hsel : IsValidSel j₀ ρL sel) (σ : Optimizer nO nL)
    {S : ℕ} (hS : 1 ≤ S) (I : Fin S → Finset ℕ) (x : Fin S → Fin nO → ℝ)
    (hσ : IsPiecewiseStationary σ T S I x) :
    expect (law G σ ⟨T, ρL, j₀, sel⟩) (fun ω => maxRounds T hT fun t =>
        ∑ s, ∑ τ ∈ (I s).filter (fun τ => τ ≤ t ∧ ω.IsActive τ), ω.xi₁ G ρL (x s) τ) ≤
      2 * Real.sqrt (5 * T) *
        Real.sqrt (expect (law G σ ⟨T, ρL, j₀, sel⟩) (fun ω => maxRounds T hT fun t => ω.normZ t ^ 2)) := by sorry

end LearnVsOpt
