-- Prove2me | Theorems.Thm_HierADA_proposition_3_5
-- name    : HierADA.proposition_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T18:06:50.777364+00:00
-- url     : https://prove2.me/theorems/505fb7ee-bf52-4cdd-8ee6-648c7cc3d6f1
-- title:
--   Proposition 3.5 — accuracy on the good event
-- statement:
--   Let $\alpha,\xi\in(0,\frac1{10})$ with the parameters of Section 3.2, any block sizes $n_j$, any analyst, and let the sample blocks and the noise lie in the good event $E$ (defined through the auxiliary execution). Then the **original** mechanism, Algorithms 1–2 without correction limits, run on the same blocks and noise:
--
--   1. completes all $k$ queries; and
--   2. every public answer $a_t$ has population error less than $\alpha$:
--   $$
--   |a_t-Pf_t|<\alpha .
--   $$
--
--   Combined with $\Pr[E]\ge1-\xi$ (Theorem 3.7), this gives the accuracy guarantee of Theorem 3.8 for the hierarchical mechanism.
--
--   **Formalization Note** The original mechanism completes all $k$ queries when, for some bound $F$ on the number of scans per query, its execution answers all $k$ queries. The public answers are the clipped and rounded releases.
--
--   Differences from the source:
--   - reading: “Let α, δ < 1/10 be the accuracy and failure parameters” (p.18) → 0 < α < 1/10 and 0 < ξ < 1/10; reason: δ there is the failure parameter, called ξ in the rest of Section 3; δ is later the privacy slack τξ/(4096(p+1))
--   - reading: Algorithm 2 scans while j ≤ p and updates G_{j+1} if j + 1 ≤ p → only the edges j ∈ [1, p) are scanned and the anchor's score is never updated; reason: there is no block p + 1, the anchor's weights stay uniform (p.13), and the proof of Proposition 3.4 says that on the last edge only block p − 1 is updated (p.22)
--   - encoding: “the original mechanism completes all k queries” → there is a scan budget F for which the execution without limits answers all k queries; reason: the execution with a larger budget is the same
--   - generalization: the block sizes n_j and noise scale b chosen in Section 3.3 → arbitrary block sizes n_j; the noise is a fixed realization; reason: the deterministic argument uses neither; the paper's choice is a special case
--   - encoding: round to the grid of spacing τ/64 → nearest multiple of τ/64, ties rounded up; reason: any tie rule has rounding error at most τ/128, which is what the proof charges
--   - encoding: blocks and edges numbered from 1, multipliers 4^{j−1} → 0-based Fin p indices, multipliers 4^j; reason: renumbering only
-- source:
--   Gribelyuk–Lin–Lyu–Majid–Woodruff–Yu–Zhou, Adaptive Data Analysis and Adversarial Robustness on Insertion-Deletion Streams, preprint (version of 2026-11-03, sha256 f220ae51…), Proposition 3.5, p.22

import Mathlib
import Definitions.Def_IsRandomnessNecessaryADA_Plain_Protocol
import Definitions.Def_HierADA_params__e3298e
import Definitions.Def_HierADA_run
import Definitions.Def_HierADA_goodEvent

set_option autoImplicit false

open IsRandomnessNecessaryADA.Plain

namespace HierADA

/-- **Proposition 3.5 (Accuracy on the good event)** — Gribelyuk–Lin–Lyu–Majid–Woodruff–Yu–Zhou,
*Adaptive Data Analysis and Adversarial Robustness on Insertion-Deletion Streams*, preprint (version
of 2026-11-03, sha256 f220ae51…), Proposition 3.5, p.22.

Let `α, ξ ∈ (0, 1/10)` with the parameters of Section 3.2, and let `(S, z)` lie in the good event `E`
(defined through the auxiliary execution). Then the **original** mechanism (Algorithms 1–2 with no
correction limits) on the same blocks and noise completes all `k` queries, and every public answer
has population error less than `α`: `|a_t − D f_t| < α`.

**Formalization Note.** The original mechanism is `run` with no limit; it "completes all `k` queries"
when for some scan budget `F` the execution answers all `k` queries (`finished`). The public
answers are the clipped, rounded releases. `ξ` enters only through the standing assumption. -/
theorem proposition_3_5 {X : Type} [Fintype X] (α ξ : ℝ) (hα0 : 0 < α) (hα : α < 1 / 10)
    (hξ0 : 0 < ξ) (hξ : ξ < 1 / 10) (k : ℕ) (P : PMF X) (A : Analyst X)
    (n : Fin (params α ξ k).p → ℕ) (S : (j : Fin (params α ξ k).p) → Fin (n j) → X) (z : Noise)
    (hE : (S, z) ∈ goodEvent (params α ξ k) k P n A) :
    ∃ F : ℕ,
      (run (params α ξ k).τ n none F S z A k).finished = true ∧
      (run (params α ξ k).τ n none F S z A k).transcript.length = k ∧
      ∀ qa ∈ (run (params α ξ k).τ n none F S z A k).transcript,
        |qa.2 - populationMean P qa.1| < α := by sorry

end HierADA
