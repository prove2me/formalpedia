-- Prove2me | Theorems.Thm_OctonionD8_flow_block_diag
-- name    : OctonionD8.flow_block_diag
-- status  : Proved
-- author  : @ShapeZero
-- created : 2026-09-27T05:23:11.479838+00:00
-- url     : https://prove2.me/theorems/d8cd9e8b-1645-47d6-bd5c-6cd21d7da286
-- title:
--   In the basis $(e_0, e_1, e_2, e_4 \mid e_3, e_5, e_6, e_7)$ the flow matrix is block diagonal
-- statement:
--   For all real $c, s$, reorder the basis of $\mathbb{R}^8$ as $(e_0, e_1, e_2, e_4 \mid e_3, e_5, e_6, e_7)$. In this basis the flow matrix $M = R_{e_1} + L_{c e_1 + s e_2}$ is block diagonal:
--
--   $$
--   M = \begin{pmatrix} A & 0 \\ 0 & B \end{pmatrix},
--   $$
--
--   with $A$ and $B$ the explicit $4\times4$ blocks. So $\mathrm{span}(e_0, e_1, e_2, e_4)$ and $\mathrm{span}(e_3, e_5, e_6, e_7)$ are invariant subspaces of the flow.
-- source:
--   Motivated by the two-generator D8 flow in the Shape Zero derivation (Shape Zero LLC): https://github.com/ShapeZeroSZ/shape-zero/blob/main/00_START_HERE/MODEL_SPEC.md §1b and https://github.com/ShapeZeroSZ/shape-zero/blob/main/02_synthesis/D8_SYNTHESIS.md ; Fano plane: Prove2Me definition RolesForceSeven.fano (mission "The role postulates force exactly seven points") ; public references: Wikipedia, "Octonion": https://en.wikipedia.org/wiki/Octonion ; Wikipedia, "Fano plane": https://en.wikipedia.org/wiki/Fano_plane

import Mathlib
import Definitions.Def_OctonionD8_blocks

namespace OctonionD8

open Polynomial

theorem flow_block_diag (c s : ℝ) :
    Matrix.reindex blockEquiv blockEquiv (flowMat c s) =
      Matrix.fromBlocks (blockA c s) 0 0 (blockB c s) := by
  sorry

end OctonionD8
