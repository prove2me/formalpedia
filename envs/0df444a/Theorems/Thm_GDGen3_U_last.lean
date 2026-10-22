-- Prove2me | Theorems.Thm_GDGen3_U_last
-- name    : GDGen3.U_last
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-12T06:14:19.02049+00:00
-- url     : https://prove2.me/theorems/0ff0f453-5dbc-4909-928e-c517f87f46c4
-- title:
--   General-N certificate lemma: U_last
-- statement:
--   Lemma `U_last` of the general-N certificate (manuscript sections 4-5), stated with index sequences over ℕ so that no concrete N is ever expanded.
-- source:
--   Companion supplementary proofs, Part III: the complete curve for the final gradient norm of GD. Formalized algebraic certificate layer: GD_General.lean, namespace GDGen3.

import Mathlib
import Definitions.Def_GDGen3Base
import Theorems.Thm_GDGen3_Abar_ne_zero
import Theorems.Thm_GDGen3_ell_of_lt
import Theorems.Thm_GDGen3_am_telescope

noncomputable section

open Finset

namespace GDGen3

lemma U_last (r : ℝ) (N : ℕ) (hN : 1 ≤ N) (ξ : ℕ → ℝ) (h0 : ξ 0 = 0)
    (hpos : ∀ i : ℕ, i ≠ 0 → 0 < ξ i) : U r ξ N N = pj r N := by sorry
