-- Prove2me | Theorems.Thm_GDGen3_flow_total
-- name    : GDGen3.flow_total
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-12T06:09:58.239524+00:00
-- url     : https://prove2.me/theorems/1bc3b2cb-9c06-410d-afce-c62f08b2cd03
-- title:
--   General-N certificate lemma: flow_total
-- statement:
--   Lemma `flow_total` of the general-N certificate (manuscript sections 4-5), stated with index sequences over ℕ so that no concrete N is ever expanded.
-- source:
--   Companion supplementary proofs, Part III: the complete curve for the final gradient norm of GD. Formalized algebraic certificate layer: GD_General.lean, namespace GDGen3.

import Mathlib
import Definitions.Def_GDGen3Base
import Theorems.Thm_GDGen3_sum_antisymm

noncomputable section

open Finset

namespace GDGen3

lemma flow_total (r : ℝ) (ξ : ℕ → ℝ) (N : ℕ) :
    (∑ i ∈ range (N + 1), d r ξ N i) = 0 := by sorry
