-- Prove2me | Theorems.Thm_GroupMetrization_struble_exists_family
-- name    : GroupMetrization.struble_exists_family
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T15:23:14.291846+00:00
-- url     : https://prove2.me/theorems/7c241b9e-a652-41c3-97e1-4ea844c58617
-- title:
--   Remark A.5.2.9 (Struble) — a second countable locally compact Hausdorff group has open, bounded, symmetric sets $U_r$, $r>0$, with $U_rU_s\subset U_{r+s}$, forming a base at $e$ and exhausting $G$
-- statement:
--   **Struble's lemma on subadditive families of neighbourhoods.** Let $G$ be a Hausdorff, locally compact, second countable topological group (not necessarily abelian). Then there is a family $(U_r)_{r>0}$ of subsets of $G$, indexed by the positive real numbers, such that:
--
--   1. every $U_r$ is open, bounded and symmetric ($U_r^{-1}=U_r$);
--   2. for all real numbers $r,s>0$,
--   $$U_r\,U_s\subset U_{r+s};$$
--   3. $(U_r)_{r>0}$ is a base of neighbourhoods of the neutral element $e$;
--   4. $\bigcup_{r>0}U_r=G$.
--
--   Here a subset $B\subset G$ is called bounded if for every neighbourhood $U$ of $e$ there are finitely many $g_1,\dots,g_N\in G$ with $B\subset g_1U\cup\dots\cup g_NU$; in a Hausdorff locally compact group this holds if and only if the closure of $B$ is compact.
--
--   The open balls $U_r=\{x:\ d(e,x)<r\}$ around $e$ of a left-invariant metric $d$ inducing the topology of $G$, all of whose balls are relatively compact, form such a family; the statement is thus the set-theoretic counterpart of Struble's theorem that second countable locally compact groups carry such metrics. The source records it in Remark A.5.2.9 (spherical boundedness and second countability), with the attribution to Struble; on the platform the metric form is `GroupMetrization.struble`.
--
--   **Formalization Note.** The family is a function `U : ℝ → Set G` of which only the values at $r>0$ are constrained. Boundedness of $U_r$ is stated in the equivalent form `IsCompact (closure (U r))`; item 3 is `(𝓝 (1 : G)).HasBasis (fun r => 0 < r) U`, and item 4 is `(⋃ r ∈ Set.Ioi 0, U r) = Set.univ`.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 571, Remark A.5.2.9 (last paragraph); classical reference: R. A. Struble, Metrics in locally compact groups, Compositio Math. 28 (1974), no. 3, pp. 217-222, Lemma 2, p. 218 (as cited by the paper)

import Mathlib

open MeasureTheory Metric Filter Topology Pointwise
open scoped ENNReal NNReal

set_option autoImplicit false

namespace GroupMetrization

theorem struble_exists_family (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] :
    ∃ U : ℝ → Set G,
      (∀ r : ℝ, 0 < r → IsOpen (U r) ∧ IsCompact (closure (U r)) ∧ (U r)⁻¹ = U r) ∧
      (∀ r s : ℝ, 0 < r → 0 < s → U r * U s ⊆ U (r + s)) ∧
      (𝓝 (1 : G)).HasBasis (fun r : ℝ => 0 < r) U ∧
      (⋃ r ∈ Set.Ioi (0 : ℝ), U r) = Set.univ := by sorry

end GroupMetrization
