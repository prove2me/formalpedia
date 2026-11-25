-- Prove2me | Theorems.Thm_MooreGraphs_eigen_cubic
-- name    : MooreGraphs.eigen_cubic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T12:19:43.115081+00:00
-- url     : https://prove2.me/theorems/bed1031c-eba6-5b8d-98b5-f372a2d8a516
-- title:
--   Moore Graphs: eigen cubic
-- statement:
--   The Moore Graphs construction uses the eigen cubic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/moore-graphs-hoffman-singleton/blob/8819ccfea5474fab3d1cbc17e703860a4e008254/MooreLib/MooreGraphsAux.lean#L165-L184
-- source:
--   https://github.com/jtraverso/moore-graphs-hoffman-singleton/blob/8819ccfea5474fab3d1cbc17e703860a4e008254/MooreLib/MooreGraphsAux.lean#L165-L184

module
public import Mathlib
public import Definitions.Def_MooreLib_MooreGraphsAux
set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph Matrix
open MooreGraphs
variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem MooreGraphs.eigen_cubic {n k : ℕ} (hsrg : G.IsSRGWith n k 0 1) {μ : ℝ}
    {x : V → ℝ} (hx0 : x ≠ 0) (hx : adjMatrix ℝ G *ᵥ x = μ • x) :
    (μ ^ 2 + μ - (k - 1)) * (μ - k) = 0 := by sorry
