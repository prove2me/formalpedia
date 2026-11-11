-- Prove2me | Theorems.Thm_LogitRankDistill_claim_5_13
-- name    : LogitRankDistill.claim_5_13
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T05:59:37.859863+00:00
-- url     : https://prove2.me/theorems/f8544849-b248-4526-8517-743f5222ed58
-- title:
--   Claim 5.13 — every future in F̃_t is y′_t ∘ y^{(i)}_{t+1:r−1} ∘ y′_r
-- statement:
--   At all epochs $k$ of Algorithm 1 and for each $t\in[T]$, each element of $\tilde F_t$ may be written as
--   $$y'_t\circ y^{(i)}_{t+1:r-1}\circ y'_r$$
--   for some $r\ge t$, some $i\in[N]$ (a draw of the coupling of Lemma 5.12) and some $y'_t,y'_r\in\Sigma$.
--   It is the step of Lemma 5.12's proof that handles the DistSpanner queries.
--
--   **Formalization Note.** Stated for every run with admissible rules and every executed epoch; $i$ ranges over the stream cells the run reads.
--
--   Differences from the source:
--   - reading: r ≥ t with y′_t ∘ y^{(i)}_{t+1:r−1} ∘ y′_r → for r = t the element is the single token y′_t; reason: the initial futures {y_t} have length 1; at r = t the positions t and r coincide
--   - generalization: Algorithm 1 run with the parameters of §5.2 → any parameters, any oracle and every admissible choice rule set; reason: the claim follows from Lines 1, 3 and 15 alone; §5.2 is a special case
--   - encoding: some i ∈ [N] (the samples of Lemma 5.12's coupling) → i < the number of stream draws read by the run; reason: the stream realises the coupling of Lemma 5.12
--   - reading: Algorithm 1, Line 14: s, r ∈ [t + 1] with r ≥ s → the test ranges over 2 ≤ s ≤ t, s ≤ r ≤ t + 1 (LogitRankDistill.Algorithms); reason: at s = 1 the tested difference is 0 (c_1 = e_1, L_{1,i} = L_oracle(·)); at s = t + 1 no coefficients c_{t+1} exist
--   - reading: F̃_T = F̂_T ∪ (Σ ∘ F̂_{T+1}) with F̂_{T+1} never initialized; DistSpanner output "padded with duplicates" to d̄ vectors → F̂_{T+1} = ∅; the padding repeats the first spanner member; reason: Line 1 initializes F̂_t only for t ∈ [T]; any duplicate of a member leaves the spanned set unchanged
-- source:
--   Golowich, Liu, Shetty, Provably Distilling from Modern Language Models via Low Logit Rank, manuscript of November 3, 2026 (arXiv:2512.09892; sha256 2ce0606e…), p. 32, Claim 5.13

import Mathlib
import Definitions.Def_LogitRankDistill_Models
import Definitions.Def_LogitRankDistill_Spanners
import Definitions.Def_LogitRankDistill_Algorithms

namespace LogitRankDistill

/-- **Claim 5.13** (p. 32): at every epoch of Algorithm 1 and every `t ∈ [T]`, each element of
`F̃_t` is `y'_t ∘ y^{(i)}_{t+1:r−1} ∘ y'_r` for some `r ≥ t`, some draw `i ∈ [N]` (among the draws
read, Lemma 5.12's coupling) and some `y'_t, y'_r ∈ Σ`; at `r = t` the element is the single token
`y'_t`. -/
theorem claim_5_13 {Tok : Type*} [Fintype Tok] [DecidableEq Tok] (C : Ctx Tok)
    (hR : C.R.Admissible) (e : Epoch Tok) (he : e ∈ C.run.epochs) (t : ℕ) (ht : 1 ≤ t)
    (htT : t ≤ C.T) :
    ∀ f ∈ tilde e.Fhat t, ∃ (r i : ℕ) (y y' : Tok), t ≤ r ∧ i < C.run.cur ∧
      f = (if r = t then [y] else [y] ++ seg (C.ω i) (t + 1) (r - 1) ++ [y']) := by sorry

end LogitRankDistill
