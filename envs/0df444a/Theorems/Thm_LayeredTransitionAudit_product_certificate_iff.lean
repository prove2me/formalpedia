-- Prove2me | Theorems.Thm_LayeredTransitionAudit_product_certificate_iff
-- name    : LayeredTransitionAudit.product_certificate_iff
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T20:54:14.935111+00:00
-- url     : https://prove2.me/theorems/b6b79efd-dea4-4f60-b322-df8ae9c457c6
-- title:
--   Bounded layered certificates for agreement on all admissible words
-- statement:
--   Consider two deterministic layered transition diagrams with finite state spaces of sizes L and R. Both diagrams process the same word of length n, with an allowed set of symbols at each position. Their terminal outputs agree on every admissible word exactly when their synchronized product has a layered certificate containing the initial pair, closed under all allowed steps, and ending only at pairs with equal outputs. The certificate uses at most (n + 1) L R state-pair mentions in total.
-- source:
--   The finite-automata product construction and the characterization of reachable states by forward-closed sets.

import Definitions.Def_LayeredTransitionAudit

open LayeredTransitionAudit

theorem LayeredTransitionAudit.product_certificate_iff {A Left Right Value : Type*}
    [DecidableEq Left] [Fintype Left] [DecidableEq Right] [Fintype Right]
    (allowed : ℕ → Finset A) (left : ℕ → Left → A → Left)
    (right : ℕ → Right → A → Right) (p : Left) (q : Right) (width : ℕ)
    (readLeft : Left → Value) (readRight : Right → Value) :
    (∃ layers : ℕ → Finset (Left × Right),
      ClosedLayers allowed (productStep left right) (p,q) width layers
        (fun s => readLeft s.1 = readRight s.2) ∧
      (∑ i ∈ Finset.range (width + 1), (layers i).card) ≤
        (width + 1) * (Fintype.card Left * Fintype.card Right)) ↔
    (∀ word : List A, word.length = width → acceptsWord allowed 0 word →
      readLeft (run left 0 p word) = readRight (run right 0 q word)) := by sorry
