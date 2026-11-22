-- Prove2me | Theorems.Thm_NormedVectorLattice_isGLB_of_antitone_tendsto
-- name    : NormedVectorLattice.isGLB_of_antitone_tendsto
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:16:30.479824+00:00
-- url     : https://prove2.me/theorems/9104a185-4f75-4f2f-898e-66336cb6157b
-- title:
--   Normed Vector Lattice: is GLB of antitone tendsto
-- statement:
--   Antitone Convergence Lemma: a decreasing sequence converging in norm is a greatest
--   lower bound for its range.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Normed.lean#L112-L115
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Normed.lean#L112-L115

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Basic
public import Mathlib.Analysis.Normed.Order.Lattice
public import Mathlib.Analysis.Normed.Module.Completion
public import Mathlib.Topology.Order.MonotoneConvergence
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Normed
set_option autoImplicit true
@[expose] public section
public section
open NormedVectorLattice
variable {X : Type*} [NormedAddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [NormedVectorLattice X]

theorem NormedVectorLattice.isGLB_of_antitone_tendsto {u : ℕ → X} {l : X}
    (hanti : Antitone u) (hlim : Filter.Tendsto u Filter.atTop (nhds l)) :
    IsGLB (Set.range u) l := by sorry
