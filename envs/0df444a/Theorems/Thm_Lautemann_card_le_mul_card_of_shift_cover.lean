-- Prove2me | Theorems.Thm_Lautemann_card_le_mul_card_of_shift_cover
-- name    : Lautemann.card_le_mul_card_of_shift_cover
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T06:46:38.916936+00:00
-- url     : https://prove2.me/theorems/c1f5f134-373f-4eab-a50b-ee5b16bb71f2
-- title:
--   Necessary density for a translate cover of a finite group
-- statement:
--   Let $A$ be a subset of a finite group $G$. If there are $t$ shifts such that for every $x\in G$ at least one $xs_j$ belongs to $A$, then $|G|\le t|A|$. The shifts may repeat and multiplication is on the right.
--
--   Thus $\lceil |G|/|A|\rceil$ is a lower bound on the number of translates in any cover with $A$ nonempty.
-- source:
--   Finite-group version of the small-set counting argument in E. Blais, Models of Computation, BPP and the Polynomial Hierarchy, Lemma 1, https://cs.uwaterloo.ca/~eblais/cs365/w26/P-and-BPP. Local source: PvsNPSeedCover.lean, density_of_shift_cover. Original Lean declaration starts at line 32. Boolean-cube specialization: https://prove2.me/theorems/96df9c3f-d784-45b5-8ffb-ddad1eb9f159.

import Mathlib

theorem Lautemann.card_le_mul_card_of_shift_cover {G : Type*} [Group G] [Fintype G]
    (pass : G → Bool) (t : ℕ) (shifts : Fin t → G)
    (each : ∀ seed : G, ∃ j, pass (seed * shifts j) = true) :
    Fintype.card G ≤ t * Fintype.card {r : G // pass r = true} := by sorry
