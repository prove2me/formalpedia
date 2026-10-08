-- Prove2me | Theorems.Thm_OAI_SnakyCertificate_certificate_correct
-- name    : OAI.SnakyCertificate.certificate_correct
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:33:23.414197+00:00
-- url     : https://prove2.me/theorems/c5e790f7-904e-40dd-a7f5-ba72d31e941b
-- statement:
--   The theorem states that a finite computational certificate for the six-cell "snaky" polyomino {(0,0),(1,0),(2,0),(3,0),(3,1),(4,1)} in ℤ² holds, as a conjunction of seven facts. The certificate is a table of 610 entries indexed 6 through 615, each a nonempty list of terms (child index, one of 8 axis-swap/reflection orientations, and x and y shifts given by digits minus 4); each row is built recursively, with rows 0 to 5 being base rows (the snaky cells translated so the i-th base point sits at the origin, with the origin removed from the required set A, the full envelope as H, and height 1), and a later row forking the oriented, shifted rows of its children: A is the union of the children's A together with the intersection of their H's, minus the origin; H is the union of the children's H together with the origin; and the height is one plus the maximum child height. The theorem asserts: (1) the table is valid, meaning it has size 610, each entry has the right index, a nonempty term list, and only children with smaller index; (2) the total number of terms over all entries is 1837; (3) row 557 has A = {(-1,0)}, |H| = 118, height 19, and H avoids all points with x ≤ -3 and y ≤ -2; (4) row 595 has A = {(-1,0)}, |H| = 222, height 27, and H avoids all points with x = -2 and y ≤ -2; (5) row 603 has A = {(-1,0)}, |H| = 275, height 27, and H avoids all points with x ≤ -3 and y = 0; (6) row 615 has A = {(1,0)}, |H| = 686, height 34, and H does not contain the point (1,-1); and (7) for every row index below 616, A is a subset of H, the origin lies in H but not in A, and the height is at most 34.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/SnakyCertificate.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/SnakyCertificate.lean; bytes 69980..70316
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_SnakyCertificate

namespace OAI

namespace SnakyCertificate

theorem certificate_correct :
    TableValid ∧ placementCount = 1837 ∧
    Output 557 (-1, 0) 118 19 {p | p.1 ≤ -3 ∧ p.2 ≤ -2} ∧
    Output 595 (-1, 0) 222 27 {p | p.1 = -2 ∧ p.2 ≤ -2} ∧
    Output 603 (-1, 0) 275 27 {p | p.1 ≤ -3 ∧ p.2 = 0} ∧
    Output 615 (1, 0) 686 34 {(1, -1)} ∧
    AllRows := by
  sorry

end SnakyCertificate
end OAI
