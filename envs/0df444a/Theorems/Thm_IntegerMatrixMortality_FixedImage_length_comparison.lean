-- Prove2me | Theorems.Thm_IntegerMatrixMortality_FixedImage_length_comparison
-- name    : IntegerMatrixMortality.FixedImage.length_comparison
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T14:34:08.969957+00:00
-- url     : https://prove2.me/theorems/651d3f1a-b434-4028-884e-8b353239da58
-- title:
--   Lemma C.3 — Length comparison including false splits
-- statement:
--   Let p≥7 be prime, k∈{2,3,5}, n≥1 and 1≤b≤n. Set a=n−b and Q=a+1. On zₙ, delete b zeros, apply T, perform k marker-one scans, apply T⁻¹, perform a marker-two scan and negate. Completion in V is equivalent to
--
--   $$b=(k-1)Q\quad\text{or}\quad(k=5\text{ and }Q<b<2Q).$$
--
--   In the first case every completed path has output X_{a,(k−1)Q−1}. Every local value before the final marker-two deletion, including every valid prefix of a rejected guess, has residue in {0,1,2}. The exceptional five-scan branch is retained.
--
--   Differences from the source:
--   - encoding: the chosen prefix and comparison scans → a valid table walk whose first arrival at marker phase 3 occurs after b deletions; reason: this counts the exit deletion and retains every rejected valid prefix
-- source:
--   Thanin Quartz, Ivan O. Shevchenko, Hans De Sterck, Jun Liu, STOC 2027 submission #1062 (October 2026), Lemma C.3, PDF p. 22 / printed p. 20

import Definitions.Def_IntegerMatrixMortality_FixedImage_ScanInterfaces

set_option autoImplicit false

namespace IntegerMatrixMortality.FixedImage

theorem length_comparison
    (p k n b : ℕ) (hp : Nat.Prime p) (hp7 : 7 ≤ p)
    (hk : k ∈ ({2,3,5} : Finset ℕ)) (hn : 1 ≤ n) (hb : 1 ≤ b) (hbn : b ≤ n) :
      let a := n-b
      let Q := a+1
      ((∃ y, CompletesWithGuess p (pureComparison k) b (some (unaryCode p n)) y) ↔
        b = (k-1)*Q ∨ (k = 5 ∧ Q < b ∧ b < 2*Q)) ∧
      (b = (k-1)*Q → ∀ y,
        CompletesWithGuess p (pureComparison k) b (some (unaryCode p n)) y →
          y = some (intermediateCode p a ((k-1)*Q-1))) ∧
      (∀ w r y, ValidWalk p (pureComparison k).edges 0 (some (unaryCode p n)) w r y →
        r ≠ 1 → InResidues p y {0,1,2}) := by sorry

end IntegerMatrixMortality.FixedImage
