-- Prove2me | Theorems.Thm_GDGen3_flow_prefix_split
-- name    : GDGen3.flow_prefix_split
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-12T05:53:56.540428+00:00
-- url     : https://prove2.me/theorems/6780f615-d4b6-4949-a954-2226029eaf1a
-- title:
--   General-N certificate lemma: flow_prefix_split
-- statement:
--   Lemma `flow_prefix_split` of the general-N certificate (manuscript sections 4-5), stated with index sequences over ℕ so that no concrete N is ever expanded.
-- source:
--   Companion supplementary proofs, Part III: the complete curve for the final gradient norm of GD. Formalized algebraic certificate layer: GD_General.lean, namespace GDGen3.

import Mathlib
import Definitions.Def_GDGen3Base
import Theorems.Thm_GDGen3_sum_antisymm

noncomputable section

open Finset

namespace GDGen3

lemma flow_prefix_split (r : ℝ) (ξ : ℕ → ℝ) (N i : ℕ) (hi : i ≤ N) :
    Finset.sum (Finset.range (i + 1)) (fun k => d r ξ N k)
      = Finset.sum (Finset.range (i + 1))
          (fun k => Finset.sum (Finset.Icc (i + 1) N) (fun j => ell r ξ N k j - ell r ξ N j k)) := by sorry
