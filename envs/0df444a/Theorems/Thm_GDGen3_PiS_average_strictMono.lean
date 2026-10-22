-- Prove2me | Theorems.Thm_GDGen3_PiS_average_strictMono
-- name    : GDGen3.PiS_average_strictMono
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-12T06:25:51.940851+00:00
-- url     : https://prove2.me/theorems/c10be6fc-9fd5-49a1-b8f7-9d11a6ac9811
-- title:
--   General-N certificate lemma: PiS_average_strictMono
-- statement:
--   Lemma `PiS_average_strictMono` of the general-N certificate (manuscript section 3), stated with index sequences over ℕ so that no concrete N is ever expanded.
-- source:
--   Companion supplementary proofs, Part III: the complete curve for the final gradient norm of GD. Formalized algebraic certificate layer: GD_General.lean, namespace GDGen3.

import Mathlib
import Definitions.Def_GDGen3Base

noncomputable section

open Finset

namespace GDGen3

lemma PiS_average_strictMono (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    StrictMono (fun n : ℕ => PiS r (n + 1) / (((n : ℝ) + 1) * ((n : ℝ) + 2))) := by sorry
