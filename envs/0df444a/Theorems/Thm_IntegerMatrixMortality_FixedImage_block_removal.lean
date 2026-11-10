-- Prove2me | Theorems.Thm_IntegerMatrixMortality_FixedImage_block_removal
-- name    : IntegerMatrixMortality.FixedImage.block_removal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T14:34:21.57522+00:00
-- url     : https://prove2.me/theorems/920c212d-d983-46fc-bc61-acc570b24ffc
-- title:
--   Proposition D.2 — Block removal rejects false splits
-- statement:
--   For every prime p≥7, adjoining (D.3) to the comparison table (D.2) gives 18 listed generators; adjoining (D.4) gives 20. Their respective updates are
--
--   $$z_{5a+4}\longmapsto X_{a,3a+2},\qquad z_{5a+4}\longmapsto X_{a,2a+1}.$$
--
--   For either table and every n∈ℕ, a path from entry to its private output join stays in V exactly on inputs n=5a+4 for some a∈ℕ. Every completed path has the displayed output. The join is not yet the program boundary.
--
--   Differences from the source:
--   - encoding: the one-block and two-block removal tables → a Boolean selecting those two exact finite edge lists; reason: false means one block and true means two blocks; both cases are asserted
-- source:
--   Thanin Quartz, Ivan O. Shevchenko, Hans De Sterck, Jun Liu, STOC 2027 submission #1062 (October 2026), Proposition D.2, PDF p. 27 / printed p. 25

import Definitions.Def_IntegerMatrixMortality_FixedImage_ScanInterfaces

set_option autoImplicit false

namespace IntegerMatrixMortality.FixedImage

theorem block_removal
    (p : ℕ) (hp : Nat.Prime p) (hp7 : 7 ≤ p) :
      (blockRemoval false).edges.length = 18 ∧ (blockRemoval true).edges.length = 20 ∧
      ∀ two : Bool, ∀ n : ℕ,
        ((∃ y, Completes p (blockRemoval two) (some (unaryCode p n)) y) ↔
          ∃ a : ℕ, n = 5*a+4) ∧
        (∀ a y, n = 5*a+4 → Completes p (blockRemoval two) (some (unaryCode p n)) y →
          y = some (intermediateCode p a (if two then 2*a+1 else 3*a+2))) := by sorry

end IntegerMatrixMortality.FixedImage
