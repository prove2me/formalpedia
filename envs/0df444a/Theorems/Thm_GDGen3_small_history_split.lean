-- Prove2me | Theorems.Thm_GDGen3_small_history_split
-- name    : GDGen3.small_history_split
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-12T06:46:57.624563+00:00
-- url     : https://prove2.me/theorems/9df9bd7c-337e-4497-b0e5-665f4228c1bf
-- title:
--   General-N certificate lemma: small_history_split
-- statement:
--   Lemma `small_history_split` of the general-N certificate (manuscript section 6), stated with index sequences over ℕ so that no concrete N is ever expanded.
-- source:
--   Companion supplementary proofs, Part III: the complete curve for the final gradient norm of GD. Formalized algebraic certificate layer: GD_General.lean, namespace GDGen3.

import Mathlib
import Definitions.Def_GDGen3Base
import Definitions.Def_GDGen3RootBase

noncomputable section

open Finset

namespace GDGen3

lemma small_history_split (N : ℕ) (a s h : ℝ) (he : h = s * a) (f q : ℕ → ℝ) :
    smallK N h f q = scaledK N a s f q
      + (1 - s) * ((∑ i ∈ range N, q i) - (N : ℝ) * q N) := by sorry
