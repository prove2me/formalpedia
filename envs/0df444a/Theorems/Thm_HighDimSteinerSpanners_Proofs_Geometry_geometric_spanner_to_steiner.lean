-- Prove2me | Theorems.Thm_HighDimSteinerSpanners_Proofs_Geometry_geometric_spanner_to_steiner
-- name    : HighDimSteinerSpanners.Proofs.Geometry.geometric_spanner_to_steiner
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:46:43.628596+00:00
-- url     : https://prove2.me/theorems/c340e97f-a0c0-44ca-be30-34a15d736c73
-- title:
--   Geometry: geometric spanner to steiner
-- statement:
--   A geometric spanner is a nonmetric Steiner spanner with no added vertices and
--   no increase in edge count, provided `lpDist` agrees with the standard `WithLp` distance.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/SteinerSpanners/Geometry.lean#L80-L159
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/SteinerSpanners/Geometry.lean#L80-L159

module
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum
public import Mathlib.Combinatorics.SimpleGraph.Walk.Maps
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Definitions.Def_LeanPool_SteinerSpanners_Defs
public import Definitions.Def_LeanPool_SteinerSpanners_Geometry
set_option autoImplicit true
@[expose] public section
public section
open scoped ENNReal
open HighDimSteinerSpanners
open HighDimSteinerSpanners HighDimSteinerSpanners.Proofs HighDimSteinerSpanners.Proofs.Geometry
noncomputable section

theorem HighDimSteinerSpanners.Proofs.Geometry.geometric_spanner_to_steiner
    (h_lp : ∀ (p : ℝ), 1 ≤ p →
      ∀ {d : ℕ} (x y : Fin d → ℝ),
        lpDist p x y =
          dist (WithLp.toLp (ENNReal.ofReal p) x) (WithLp.toLp (ENNReal.ofReal p) y))
    {p : ℝ} (hp : 1 ≤ p) {n d : ℕ} (P : Fin n → (Fin d → ℝ)) (C : ℝ)
    (G : SimpleGraph (Fin n)) (hGeom : IsGeometricSpanner p P C G) :
    ∃ (H : SimpleGraph (Fin n ⊕ PEmpty)) (w : Sym2 (Fin n ⊕ PEmpty) → ℝ),
      IsNonMetricSteinerSpanner p P C H w ∧
      (Nat.card H.edgeSet : ℝ) ≤ (Nat.card G.edgeSet : ℝ) := by sorry
