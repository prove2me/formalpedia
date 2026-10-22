-- Prove2me | Theorems.Thm_GDGen3_ginner_backward
-- name    : GDGen3.ginner_backward
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-12T06:44:30.129478+00:00
-- url     : https://prove2.me/theorems/6a579d5c-5413-4627-858a-d5bd14edc2be
-- title:
--   General-N certificate lemma: ginner_backward
-- statement:
--   Lemma `ginner_backward` of the general-N certificate (manuscript section 6), stated with index sequences over ℕ so that no concrete N is ever expanded.
-- source:
--   Companion supplementary proofs, Part III: the complete curve for the final gradient norm of GD. Formalized algebraic certificate layer: GD_General.lean, namespace GDGen3.

import Mathlib
import Definitions.Def_GDGen3Base

noncomputable section

open Finset

namespace GDGen3

lemma ginner_backward (h : ℝ) (P : ℕ → ℕ → ℝ) (i : ℕ) : ginner h P (i + 1) i = -h * P i i := by sorry
