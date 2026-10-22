-- Prove2me | Theorems.Thm_GDGen3_referenceXi_pos
-- name    : GDGen3.referenceXi_pos
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-12T06:32:10.027714+00:00
-- url     : https://prove2.me/theorems/dc4f8dd3-e885-4ccb-b48e-14d992f2031d
-- title:
--   General-N certificate lemma: referenceXi_pos
-- statement:
--   Lemma `referenceXi_pos` of the general-N certificate (manuscript section 3), stated with index sequences over ℕ so that no concrete N is ever expanded.
-- source:
--   Companion supplementary proofs, Part III: the complete curve for the final gradient norm of GD. Formalized algebraic certificate layer: GD_General.lean, namespace GDGen3.

import Mathlib
import Definitions.Def_GDGen3Base
import Definitions.Def_GDGen3RootBase

noncomputable section

open Finset

namespace GDGen3

lemma referenceXi_pos (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (N i : ℕ)
    (hi : 1 ≤ i) (hiN : i < N)
    (hbranch : 1 / r ^ N ≤ 1 + (N : ℝ) * (1 + r)) : 0 < referenceXi r i := by sorry
