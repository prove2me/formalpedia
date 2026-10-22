-- Prove2me | Theorems.Thm_GDGen3_pj_slope_strictMono
-- name    : GDGen3.pj_slope_strictMono
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-12T06:21:56.157618+00:00
-- url     : https://prove2.me/theorems/bbec1374-46e1-4045-95fb-acabc3657897
-- title:
--   General-N certificate lemma: pj_slope_strictMono
-- statement:
--   Lemma `pj_slope_strictMono` of the general-N certificate (manuscript sections 4-5), stated with index sequences over ℕ so that no concrete N is ever expanded.
-- source:
--   Companion supplementary proofs, Part III: the complete curve for the final gradient norm of GD. Formalized algebraic certificate layer: GD_General.lean, namespace GDGen3.

import Mathlib
import Definitions.Def_GDGen3Base
import Theorems.Thm_GDGen3_pj_geometric
import Theorems.Thm_GDGen3_pow_slope_strictMono

noncomputable section

open Finset

namespace GDGen3

lemma pj_slope_strictMono (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    StrictMono (fun n : ℕ => pj r (n + 1) / ((n : ℝ) + 1)) := by sorry
