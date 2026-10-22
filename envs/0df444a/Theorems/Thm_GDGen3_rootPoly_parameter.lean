-- Prove2me | Theorems.Thm_GDGen3_rootPoly_parameter
-- name    : GDGen3.rootPoly_parameter
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-12T06:24:26.466136+00:00
-- url     : https://prove2.me/theorems/9ba0b857-5813-429e-947e-1e241fd6d615
-- title:
--   General-N certificate lemma: rootPoly_parameter
-- statement:
--   Lemma `rootPoly_parameter` of the general-N certificate (manuscript sections 4-5), stated with index sequences over ℕ so that no concrete N is ever expanded.
-- source:
--   Companion supplementary proofs, Part III: the complete curve for the final gradient norm of GD. Formalized algebraic certificate layer: GD_General.lean, namespace GDGen3.

import Mathlib
import Definitions.Def_GDGen3Base
import Definitions.Def_GDGen3RootBase
import Theorems.Thm_GDGen3_pj_pos

noncomputable section

open Finset

namespace GDGen3

lemma rootPoly_parameter (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (v x : ℝ) (i : ℕ) :
    rootPoly r v i x = rootPoly r (1 + r) i x
      + ((1 + r) - v) * (i + 1) / (1 + r) * ((i : ℝ) / 2 - x) := by sorry
