-- Prove2me | Theorems.Thm_GDGen3_rootXi_quad7
-- name    : GDGen3.rootXi_quad7
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-12T06:29:51.351188+00:00
-- url     : https://prove2.me/theorems/26ea6975-9c49-418f-96c4-bfdabd1a0ce9
-- title:
--   General-N certificate lemma: rootXi_quad7
-- statement:
--   Lemma `rootXi_quad7` of the general-N certificate (manuscript section 3), stated with index sequences over ℕ so that no concrete N is ever expanded.
-- source:
--   Companion supplementary proofs, Part III: the complete curve for the final gradient norm of GD. Formalized algebraic certificate layer: GD_General.lean, namespace GDGen3.

import Mathlib
import Definitions.Def_GDGen3Base
import Definitions.Def_GDGen3RootBase

noncomputable section

open Finset

namespace GDGen3

lemma rootXi_quad7 (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (N i : ℕ) (hiN : i < N) :
    pj r (i + 1) * eta r N (rootXi r N) i * (1 + rootXi r N i) = X r N (i + 1) := by sorry
