-- Prove2me | Theorems.Thm_GDGen3_referenceXi_quad
-- name    : GDGen3.referenceXi_quad
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-12T06:33:32.944981+00:00
-- url     : https://prove2.me/theorems/96aa5928-1e1e-47e3-8a8c-6fdcb586c999
-- title:
--   General-N certificate lemma: referenceXi_quad
-- statement:
--   Lemma `referenceXi_quad` of the general-N certificate (manuscript section 3), stated with index sequences over ℕ so that no concrete N is ever expanded.
-- source:
--   Companion supplementary proofs, Part III: the complete curve for the final gradient norm of GD. Formalized algebraic certificate layer: GD_General.lean, namespace GDGen3.

import Mathlib
import Definitions.Def_GDGen3Base
import Definitions.Def_GDGen3RootBase

noncomputable section

open Finset

namespace GDGen3

lemma referenceXi_quad (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (i : ℕ) :
    rootPoly r (1 + r) i (referenceXi r i) = 0 := by sorry
