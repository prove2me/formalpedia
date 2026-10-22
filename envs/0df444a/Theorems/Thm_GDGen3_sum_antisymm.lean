-- Prove2me | Theorems.Thm_GDGen3_sum_antisymm
-- name    : GDGen3.sum_antisymm
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-12T05:47:43.642876+00:00
-- url     : https://prove2.me/theorems/f5df813f-7ea6-453d-bc46-05dd902556aa
-- title:
--   General-N certificate lemma: sum_antisymm
-- statement:
--   Lemma `sum_antisymm` of the general-N certificate (manuscript sections 4-5), stated with index sequences over ℕ so that no concrete N is ever expanded.
-- source:
--   Companion supplementary proofs, Part III: the complete curve for the final gradient norm of GD. Formalized algebraic certificate layer: GD_General.lean, namespace GDGen3.

import Mathlib
import Definitions.Def_GDGen3Base

noncomputable section

open Finset

namespace GDGen3

lemma sum_antisymm (F : ℕ → ℕ → ℝ) (s : Finset ℕ) :
    Finset.sum s (fun k => Finset.sum s (fun j => (F k j - F j k))) = 0 := by sorry
