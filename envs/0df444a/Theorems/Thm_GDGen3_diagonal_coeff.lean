-- Prove2me | Theorems.Thm_GDGen3_diagonal_coeff
-- name    : GDGen3.diagonal_coeff
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-12T06:11:22.217959+00:00
-- url     : https://prove2.me/theorems/babc6f23-e294-4386-b448-410d833c89f1
-- title:
--   General-N certificate lemma: diagonal_coeff
-- statement:
--   Lemma `diagonal_coeff` of the general-N certificate (manuscript sections 4-5), stated with index sequences over ℕ so that no concrete N is ever expanded.
-- source:
--   Companion supplementary proofs, Part III: the complete curve for the final gradient norm of GD. Formalized algebraic certificate layer: GD_General.lean, namespace GDGen3.

import Mathlib
import Definitions.Def_GDGen3Base
import Theorems.Thm_GDGen3_incoming_sum

noncomputable section

open Finset

namespace GDGen3

lemma diagonal_coeff (r : ℝ) (ξ : ℕ → ℝ) (N i : ℕ) (hi : i ≤ N) :
    2 * (1 + r) * V r ξ N i - (∑ j ∈ range (N + 1), (ell r ξ N i j + ell r ξ N j i))
      + 2 * ell r ξ N i i = 2 * (r * V r ξ N i - U r ξ N i) - d r ξ N i := by sorry
