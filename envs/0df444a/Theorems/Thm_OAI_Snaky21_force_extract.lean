-- Prove2me | Theorems.Thm_OAI_Snaky21_force_extract
-- name    : OAI.Snaky21.force_extract
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-08T07:52:17.603975+00:00
-- url     : https://prove2.me/theorems/900ef069-bf48-4501-afbc-5785e270706f
-- title:
--   A legal positional policy extracted from finite-horizon forcing
-- statement:
--   For a positive number N, suppose Maker can force a Snaky target within N further actual claims from the empty board, in the finite-horizon forcing relation. There exists one policy depending only on the remaining budget and the two current ownership sets, legal on every finite input. Against every reply sequence legal before the final round, Maker has a target and exactly N cells after its Nth claim, disjoint from the first N−1 Breaker cells. Before that final claim both ownership sets are disjoint and Breaker has made exactly the recorded number of claims. No Nth Breaker reply is assumed legal.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Snaky-in-21-Maker-moves-September-25-2026/article.pdf; The main theorem strategy argument and its fixed-endpoint reformulation; build/strategy.tex, section One strategy against every continuation.

import Definitions.Def_Snaky21Core
open OAI.Snaky21 OAI.SnakyPrototype OAI.SnakyPrototype.OrdinaryStrategy

theorem OAI.Snaky21.force_extract (N : ℕ) (hN : 0 < N) (hstart : CanForce N ∅ ∅) :
    ∃ σ : Policy Cell,
      (∀ r M B, σ r M B ∉ M ∧ σ r M B ∉ B) ∧
      ∀ β : ℕ → Cell, LegalRepliesBeforeFinal σ N β ∅ ∅ →
        HasSnaky (playState σ N β ∅ ∅ N).1 ∧
        (playState σ N β ∅ ∅ N).1.card = N ∧
        Disjoint (playState σ N β ∅ ∅ N).1 (playState σ N β ∅ ∅ (N - 1)).2 ∧
        ∀ k, k < N →
          Disjoint (playState σ N β ∅ ∅ k).1 (playState σ N β ∅ ∅ k).2 ∧
          (playState σ N β ∅ ∅ k).2.card = k := by sorry
