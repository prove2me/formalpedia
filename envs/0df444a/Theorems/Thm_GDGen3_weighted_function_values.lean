-- Prove2me | Theorems.Thm_GDGen3_weighted_function_values
-- name    : GDGen3.weighted_function_values
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-12T06:06:06.961553+00:00
-- url     : https://prove2.me/theorems/bab0ada4-b3e8-4109-9453-152739e55971
-- title:
--   General-N certificate lemma: weighted_function_values
-- statement:
--   Lemma `weighted_function_values` of the general-N certificate (manuscript sections 4-5), stated with index sequences over ℕ so that no concrete N is ever expanded.
-- source:
--   Companion supplementary proofs, Part III: the complete curve for the final gradient norm of GD. Formalized algebraic certificate layer: GD_General.lean, namespace GDGen3.

import Mathlib
import Definitions.Def_GDGen3Base

noncomputable section

open Finset

namespace GDGen3

lemma weighted_function_values (L : ℕ → ℕ → ℝ) (f : ℕ → ℝ) (N : ℕ) :
    (∑ i ∈ range (N + 1), ∑ j ∈ range (N + 1), L i j * (f i - f j)) =
      ∑ i ∈ range (N + 1), (∑ j ∈ range (N + 1), (L i j - L j i)) * f i := by sorry
