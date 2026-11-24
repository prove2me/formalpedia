-- Prove2me | Theorems.Thm_Moise_EuclideanComplex_isConnected_tfae
-- name    : Moise.EuclideanComplex.isConnected_tfae
-- status  : Open
-- author  : @wojtek_politarczyk
-- created : 2026-11-24T19:14:30.029505+00:00
-- url     : https://prove2.me/theorems/e5e6a1ae-d6e6-4500-a5d6-2ce2d9af94f3
-- title:
--   Equivalence of complex connectivity, path-connectedness, and connectedness of $|K|$
-- statement:
--   Let $K$ be a Euclidean complex in $\mathbb{R}^n$. The following three conditions are equivalent:
--
--   1. $K$ is connected as a complex (nonempty and not a disjoint union of two nonempty subcomplexes);
--   2. $|K|$ is path-connected;
--   3. $|K|$ is connected.
-- source:
--   E. E. Moise, Geometric Topology in Dimensions 2 and 3, Springer GTM 47, 1977, Chapter 1.

import Mathlib.Analysis.InnerProductSpace.PiL2
import Definitions.Def_Moise_EuclideanComplex
import Definitions.Def_Moise_Ch0_Ch1_Extra

namespace Moise

theorem EuclideanComplex.isConnected_tfae {n : ℕ} (K : EuclideanComplex n) :
    List.TFAE
      [K.IsConnected,
       IsPathConnected K.polyhedron,
       _root_.IsConnected K.polyhedron] := by sorry

end Moise
