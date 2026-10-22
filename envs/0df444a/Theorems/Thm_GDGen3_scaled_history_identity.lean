-- Prove2me | Theorems.Thm_GDGen3_scaled_history_identity
-- name    : GDGen3.scaled_history_identity
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-12T06:46:52.631445+00:00
-- url     : https://prove2.me/theorems/faed14b9-a7f1-42c1-b643-a8fb5f26d139
-- title:
--   General-N certificate lemma: scaled_history_identity
-- statement:
--   Lemma `scaled_history_identity` of the general-N certificate (manuscript section 6), stated with index sequences over ℕ so that no concrete N is ever expanded.
-- source:
--   Companion supplementary proofs, Part III: the complete curve for the final gradient norm of GD. Formalized algebraic certificate layer: GD_General.lean, namespace GDGen3.

import Mathlib
import Definitions.Def_GDGen3Base
import Definitions.Def_GDGen3RootBase

noncomputable section

open Finset

namespace GDGen3

lemma scaled_history_identity (N : ℕ) (a s : ℝ) (f q : ℕ → ℝ) :
    smallK N a (fun i => s * f i) (fun i => s ^ 2 * q i) = s * scaledK N a s f q := by sorry
