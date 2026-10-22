-- Prove2me | Theorems.Thm_GDGen3_flow_at_index
-- name    : GDGen3.flow_at_index
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-12T06:12:53.738866+00:00
-- url     : https://prove2.me/theorems/9fe9d906-b372-4ccb-b471-d99e6db5fdbd
-- title:
--   General-N certificate lemma: flow_at_index
-- statement:
--   Lemma `flow_at_index` of the general-N certificate (manuscript sections 4-5), stated with index sequences over ℕ so that no concrete N is ever expanded.
-- source:
--   Companion supplementary proofs, Part III: the complete curve for the final gradient norm of GD. Formalized algebraic certificate layer: GD_General.lean, namespace GDGen3.

import Mathlib
import Definitions.Def_GDGen3Base
import Theorems.Thm_GDGen3_flow_identity

noncomputable section

open Finset

namespace GDGen3

lemma flow_at_index (r : ℝ) (N : ℕ) (hN : 1 ≤ N) (ξ : ℕ → ℝ) (hr : 0 < r) (hr1 : r < 1)
    (hpos : ∀ i : ℕ, i ≠ 0 → 0 < ξ i) (h0 : ξ 0 = 0)
    (hquad : ∀ i : ℕ, i < N → pj r (i + 1) * ξ i * (1 + eta r N ξ i) = X r N i)
    (hquad7 : ∀ i : ℕ, i < N → pj r (i + 1) * eta r N ξ i * (1 + ξ i) = X r N (i + 1))
    (hpin : pj r N * ξ (N - 1) = X r N (N - 1)) (i : ℕ) (hi : i < N) :
    d r ξ N i = M r N := by sorry
