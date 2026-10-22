-- Prove2me | Theorems.Thm_GDGen3_M_boundary
-- name    : GDGen3.M_boundary
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-12T06:42:37.124995+00:00
-- url     : https://prove2.me/theorems/203893b8-e97d-4c76-9cac-8a898bd47dc0
-- title:
--   General-N certificate lemma: M_boundary
-- statement:
--   Lemma `M_boundary` of the general-N certificate (manuscript section 6), stated with index sequences over ℕ so that no concrete N is ever expanded.
-- source:
--   Companion supplementary proofs, Part III: the complete curve for the final gradient norm of GD. Formalized algebraic certificate layer: GD_General.lean, namespace GDGen3.

import Mathlib
import Definitions.Def_GDGen3Base

noncomputable section

open Finset

namespace GDGen3

lemma M_boundary (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (N : ℕ) (hN : 1 ≤ N)
    (hboundary : 1 / r ^ N = 1 + (N : ℝ) * (1 + r)) : M r N = 1 + r := by sorry
