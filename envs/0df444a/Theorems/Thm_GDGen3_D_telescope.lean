-- Prove2me | Theorems.Thm_GDGen3_D_telescope
-- name    : GDGen3.D_telescope
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-12T05:52:27.495968+00:00
-- url     : https://prove2.me/theorems/7ad3996a-fe53-44b5-a382-9b9144389e7d
-- title:
--   General-N certificate lemma: D_telescope
-- statement:
--   Lemma `D_telescope` of the general-N certificate (manuscript sections 4-5), stated with index sequences over ℕ so that no concrete N is ever expanded.
-- source:
--   Companion supplementary proofs, Part III: the complete curve for the final gradient norm of GD. Formalized algebraic certificate layer: GD_General.lean, namespace GDGen3.

import Mathlib
import Definitions.Def_GDGen3Base

noncomputable section

open Finset

namespace GDGen3

lemma D_telescope (r : ℝ) (ξ : ℕ → ℝ) (N i : ℕ) (hi : i + 1 ≤ N) :
    Finset.sum (Finset.Icc (i + 1) N) (fun j => D r ξ N j - D r ξ N (j + 1)) = D r ξ N (i + 1) := by sorry
