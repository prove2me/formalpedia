-- Prove2me | Theorems.Thm_GDGen3_ginner_forward
-- name    : GDGen3.ginner_forward
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-12T06:44:25.093158+00:00
-- url     : https://prove2.me/theorems/ef2ad45f-d22f-4b75-8a5f-34d36f1f93e1
-- title:
--   General-N certificate lemma: ginner_forward
-- statement:
--   Lemma `ginner_forward` of the general-N certificate (manuscript section 6), stated with index sequences over ℕ so that no concrete N is ever expanded.
-- source:
--   Companion supplementary proofs, Part III: the complete curve for the final gradient norm of GD. Formalized algebraic certificate layer: GD_General.lean, namespace GDGen3.

import Mathlib
import Definitions.Def_GDGen3Base

noncomputable section

open Finset

namespace GDGen3

lemma ginner_forward (h : ℝ) (P : ℕ → ℕ → ℝ) (i : ℕ) : ginner h P i (i + 1) = h * P (i + 1) i := by sorry
