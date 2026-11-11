-- Prove2me | Theorems.Thm_NecklacePPAD_Main_theorem_1_1
-- name    : NecklacePPAD.Main.theorem_1_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T04:07:18.571274+00:00
-- url     : https://prove2.me/theorems/33d6ed9a-ae79-48f9-849e-80f804b6e4b4
-- title:
--   Theorem 1.1 — Necklace-Splitting is PPAD-hard with 10 beads per colour, with 2b beads for every b ≥ 5, and with 6, 8 or 10 beads per colour
-- statement:
--   Necklace-Splitting$_{10}$ is PPAD-hard. More generally, Necklace-Splitting$_{2b}$ is PPAD-hard for every $b\ge5$, and Necklace-Splitting restricted to necklaces in which every colour occurs 6, 8 or 10 times is PPAD-hard. Here PPAD-hard means that every problem of PPAD (total search problems reducing to End-of-Line) reduces to it by a polynomial-time search reduction whose answer map is correct for every split.
--
--   Differences from the source:
--   - encoding: PPAD-hard (not defined in the paper) → CEPolytopeHard.PPADHard: every Q ∈ QuasiStrictNE.PPAD has CardinalMatching.SearchReduces Q S; reason: the standard Levin-reduction notion, the same layer as the platform statement of Theorem 3.3
--   - encoding: Necklace-Splitting₁₀, Necklace-Splitting₂b, the 6/8/10 restriction → NSCounts {10}, NSCounts {2 * b}, NSCounts {6, 8, 10} (colours Fin n, every colour occurs, answers = codes of splits); reason: the same instances and solutions in binary
-- source:
--   Zeng, Wang, Cao, Dai, Wang, Necklace Splitting with Ten Beads per Colour is PPAD-Hard (STOC 2027 submission, sha256 d5b5449c…41ac), Theorem 1.1, p. 1 (PDF 3)

import Mathlib
import Definitions.Def_NecklacePPAD_Main_NSCounts
import Definitions.Def_CEPolytopeHard_PPADHard

set_option autoImplicit false

namespace NecklacePPAD.Main

/-- **Theorem 1.1** (Zeng, Wang, Cao, Dai, Wang, *Necklace Splitting with Ten Beads per Colour is
PPAD-Hard*, STOC 2027 submission, sha256 d5b5449c…, p. 1 (PDF 3)). Necklace-Splitting₁₀ is
PPAD-hard. More generally, Necklace-Splitting₂b is PPAD-hard for every `b ≥ 5`, and
Necklace-Splitting restricted to necklaces in which every colour occurs 6, 8 or 10 times is
PPAD-hard. -/
theorem theorem_1_1 :
    CEPolytopeHard.PPADHard (NSCounts {10}) ∧
    (∀ b : ℕ, 5 ≤ b → CEPolytopeHard.PPADHard (NSCounts {2 * b})) ∧
    CEPolytopeHard.PPADHard (NSCounts {6, 8, 10}) := by sorry

end NecklacePPAD.Main
