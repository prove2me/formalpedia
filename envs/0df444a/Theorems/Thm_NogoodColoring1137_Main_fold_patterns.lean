-- Prove2me | Theorems.Thm_NogoodColoring1137_Main_fold_patterns
-- name    : NogoodColoring1137.Main.fold_patterns
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T17:02:33.671663+00:00
-- url     : https://prove2.me/theorems/cc1ce83d-6df5-4208-bbb5-9b07d093bb26
-- title:
--   Lemma 5.2 — All fold patterns and odd prefixes
-- statement:
--   For even $r\ge2$, PatternA uses only nonzero colors, different at positions 1,2 and equal in each subsequent odd/even pair. PatternB sets zero at one variable position and satisfies exactly the four source cases, including the separate $p=r=2$ case. Then every fold is defined and
--   $$\text{PatternA}\implies F_r=0,\qquad\text{PatternB}\implies F_r\in\{1,2\}.$$
--   For every positive odd prefix the analogous pattern can be chosen to give either specified nonzero final fold, including length one. Every proper connector extension has the corresponding final root color. This includes both pattern types and the odd-prefix choice used by Theorem 2.
--
--   **Formalization Note** Empty ranges impose no equalities. Patterns are indexed color words; the source construction applies them on supports of distinct terminals.
--
--   Differences from the source:
--   - generalization: the surrounding section assumes n ≥ 8 and diameter at most 2 → root assertions on every finite connector graph; reason: the fold calculations on pp.15–16 use no graph-size bound
--   - encoding: terminal color patterns and nonzero colors 1,2 → bounded one-based Fin 3 color words, nonzero expressed as inequality to zero; reason: these represent the same ranges and colors, and the proper-extension conclusions are explicit
-- source:
--   Philip Whittington, STOC 2027 submission #1137 (October 2026), Lemma 5.2, pp.15–16

import Definitions.Def_NogoodColoring1137_Main_Folds

namespace NogoodColoring1137.Main

/-- Lemma 5.2, pp.15–16: all even cases and the odd-prefix choice. -/
theorem fold_patterns :
    (∀ r, 2 ≤ r → Even r → ∀ c : ℕ → Color,
      PatternA r c → (∀ i, 1 ≤ i → i ≤ r → (FoldPrefix c i).isSome) ∧
        FoldPrefix c r = some 0) ∧
    (∀ r p, 2 ≤ r → Even r → ∀ c : ℕ → Color,
      PatternB r p c → (∀ i, 1 ≤ i → i ≤ r → (FoldPrefix c i).isSome) ∧
        ∃ a : Color, a ≠ 0 ∧ FoldPrefix c r = some a) ∧
    (∀ t, 1 ≤ t → Odd t → ∀ a : Color, a ≠ 0 →
      ∃ c : ℕ → Color,
        (∀ i, 1 ≤ i → i ≤ t → c i ≠ 0) ∧
        (3 ≤ t → c 1 ≠ c 2) ∧
        (∀ j, 1 ≤ j → 2*j+2 ≤ t → c (2*j+1) = c (2*j+2)) ∧
        (∀ i, 1 ≤ i → i ≤ t → (FoldPrefix c i).isSome) ∧ FoldPrefix c t = some a) ∧
    (∀ (n r : ℕ) (G : SimpleGraph (Fin n)) (q z : ℕ → Fin n) (C : Fin n → Color),
      Connector G r q z → Even r → (∀ v w, G.Adj v w → C v ≠ C w) →
      (PatternA r (fun j => C (q j)) → C (z r) = 0) ∧
      (∀ p, PatternB r p (fun j => C (q j)) → C (z r) ≠ 0)) := by sorry

end NogoodColoring1137.Main
