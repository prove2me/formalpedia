-- Prove2me | Theorems.Thm_GDGen3_pj_strictMono
-- name    : GDGen3.pj_strictMono
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-12T06:36:52.829807+00:00
-- url     : https://prove2.me/theorems/90c65621-725b-4321-8cf7-bc117c67b72a
-- title:
--   General-N certificate lemma: pj_strictMono
-- statement:
--   Lemma `pj_strictMono` of the general-N certificate (manuscript section 3), stated with index sequences over ℕ so that no concrete N is ever expanded.
-- source:
--   Companion supplementary proofs, Part III: the complete curve for the final gradient norm of GD. Formalized algebraic certificate layer: GD_General.lean, namespace GDGen3.

import Mathlib
import Definitions.Def_GDGen3Base

noncomputable section

open Finset

namespace GDGen3

lemma pj_strictMono (r : ℝ) (hr : 0 < r) (hr1 : r < 1) : StrictMono (pj r) := by sorry
