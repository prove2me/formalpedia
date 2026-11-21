-- Prove2me | Theorems.Thm_MasulloGRH_compact_disk_bidual_representation
-- name    : MasulloGRH.compact_disk_bidual_representation
-- status  : Proved
-- author  : @ghseeli
-- created : 2026-11-20T23:47:37.081636+00:00
-- url     : https://prove2.me/theorems/54edc42e-51e7-4f7c-9971-efc65bece2cc
-- title:
--   Compact disks represent dominated functionals on the strong dual
-- statement:
--   Let $E$ be a complex topological vector space and let $K\subseteq E$ be compact, convex, balanced, and contain $0$. Let $F$ be a continuous linear functional on the strong dual $E'_\beta$. Suppose every uniform bound for a continuous linear functional on $K$ also bounds its value under $F$: for every $f\in E'$ and $r\ge0$,
--
--   $$\bigl(|f(y)|\le r\text{ for every }y\in K\bigr)\implies |F(f)|\le r.$$
--
--   Then there exists $y\in K$ such that
--
--   $$F(f)=f(y)\qquad\text{for every }f\in E'.$$
--
--   This compact-disk representation principle isolates the separation argument behind semi-reflexivity of spaces whose bounded sets have compact closure. It needs neither nuclearity nor metrizability, and does not require $E$ to be Hausdorff.
-- source:
--   Compact bipolar/representation principle, proved here from the weak representation theorem and geometric Hahn–Banach separation. Exact Mathlib sources at revision 0df444a360eaa60ab8c11dca51a86af692955474: Mathlib/Analysis/LocallyConvex/WeakDual.lean (LinearMap.dualEmbedding_surjective) and Mathlib/Analysis/LocallyConvex/Separation.lean (RCLike.geometric_hahn_banach_closed_point), https://github.com/leanprover-community/mathlib4/tree/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/LocallyConvex . Supporting context: Masullo, The Music of the Primes, frozen 20 November 2026 draft, paragraph before Lemma C.2.4.16, p. 690, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf. This lemma is an extracted general argument, not a numbered statement in Masullo.

import Definitions.Def_MasulloGRH_LocallyConvex
set_option autoImplicit false
open MasulloGRH Topology Filter Set
open scoped ComplexOrder

theorem MasulloGRH.compact_disk_bidual_representation (E : Type*) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] (K : Set E) (hK : IsCompact K) (hconv : Convex ℝ K)
    (hbal : Balanced ℂ K) (h0 : (0 : E) ∈ K)
    (F : StrongDual ℂ (StrongDual ℂ E))
    (hF : ∀ (f : StrongDual ℂ E) (r : ℝ), 0 ≤ r →
      (∀ y ∈ K, ‖f y‖ ≤ r) → ‖F f‖ ≤ r) :
    ∃ y ∈ K, ∀ f : StrongDual ℂ E, F f = f y := by sorry
