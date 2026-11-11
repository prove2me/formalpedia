-- Prove2me | Theorems.Thm_MinDilationTree_Sublinear_mst_upper_bound
-- name    : MinDilationTree.Sublinear.mst_upper_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:25:36.56258+00:00
-- url     : https://prove2.me/theorems/fb9696fc-16d2-49b7-b0f0-8dc93185a6f7
-- title:
--   §3 MST upper bound [26]
-- statement:
--   Let $S=\{p_0,\ldots,p_{n-1}\}$ be a nonempty set of distinct points in the Euclidean plane. Let $T$ be any spanning tree whose total Euclidean edge length is minimum among all spanning trees of $S$. Then
--
--   $$
--   \operatorname{dil}(T)\le n-1.
--   $$
--
--   This provides the dilation bound for the MST returned by the early exits in the main approximation algorithm. Collinear and cocircular inputs are included. For $n=1$, the maximum over distinct pairs is empty and has value zero.
--
--   Differences from the source:
--   - encoding: a set S of n points and its Euclidean MST → an injective map Fin n → EuclideanSpace ℝ (Fin 2), with 1 ≤ n, and the published MST predicate on the complete graph; reason: labels enumerate the same points; nonemptiness excludes the empty-tree convention and introduces no restriction on the source’s MST inputs
--   - encoding: the maximum pair dilation is at most n − 1 → the maximum in ℝ≥0∞ is bounded by ENNReal.ofReal ((n : ℝ) − 1); reason: the finite connected tree has finite distances; at n = 1 both empty maxima are interpreted as zero
-- source:
--   Sarita de Berg, Jacobus Conradi, Peter Kramer, André Nusser, Sampson Wong, STOC 2027 submission #185 (October 2026), p. 4 (PDF p. 5), §3, MST upper bound [26]

import Mathlib
import Definitions.Def_MinDilationTree_Sublinear_GeometricGraph

set_option autoImplicit false

namespace MinDilationTree.Sublinear

/-- §3, p.4 (PDF 5), MST upper bound [26]. At n = 1 the empty maximum is 0.
The nonempty finite input is the source's set; no condition on its geometric position is added. -/
theorem mst_upper_bound {n : ℕ} (hn : 1 ≤ n) (p : Fin n → Plane)
    (hp : Function.Injective p) (T : SimpleGraph (Fin n)) (hT : IsEuclideanMST p T) :
    dilation p T ≤ ENNReal.ofReal ((n : ℝ) - 1) := by sorry

end MinDilationTree.Sublinear
