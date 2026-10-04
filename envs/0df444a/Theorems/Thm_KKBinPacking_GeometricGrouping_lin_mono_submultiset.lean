-- Prove2me | Theorems.Thm_KKBinPacking_GeometricGrouping_lin_mono_submultiset
-- name    : KKBinPacking.GeometricGrouping.lin_mono_submultiset
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-02T13:56:23.507166+00:00
-- url     : https://prove2.me/theorems/d7889526-c21e-464e-bfa8-9e6ec5122d65
-- title:
--   Configuration LP monotonicity under deletion of item occurrences
-- statement:
--   Let $A$ and $B$ be finite multisets of item sizes in $(0,1)$, and suppose that $A$ is a submultiset of $B$, so that each size occurs in $A$ no more often than it occurs in $B$. For the configuration linear program with nonnegative weights and unit-capacity configurations,
--
--   $$LIN(A)\le LIN(B).$$
--
--   Deleting item occurrences therefore cannot increase the fractional packing optimum. This includes deletion of an entire item type and deletion of every item, and supplies a reusable comparison for filtered and residual instances in bin-packing algorithms.
--
--   **Formalization Note** Configurations are nonempty and may repeat an item type more often than that type occurs in the instance; the result respects both conventions of the shared configuration LP definition.
-- source:
--   A basic monotonicity property of the configuration LP used by Karmarkar and Karp, An Efficient Approximation Scheme for the One-Dimensional Bin-Packing Problem, FOCS 1982, p. 313, LP (I). https://pagesperso.g-scop.grenoble-inp.fr/~newmana/OptApproxFall2016/Karmarker-Karp-BinPacking.pdf

import Definitions.Def_KKBinPacking_GeometricGrouping_Instance
import Definitions.Def_KKBinPacking_Shared_ConfigLP
open KKBinPacking.Shared

namespace KKBinPacking.GeometricGrouping
theorem lin_mono_submultiset (A B : Multiset ℝ) (hA : IsInstance A) (hB : IsInstance B)
    (hAB : A ≤ B) : LIN A ≤ LIN B := by sorry
end KKBinPacking.GeometricGrouping
