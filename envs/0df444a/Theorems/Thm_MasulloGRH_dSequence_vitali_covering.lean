-- Prove2me | Theorems.Thm_MasulloGRH_dSequence_vitali_covering
-- name    : MasulloGRH.dSequence_vitali_covering
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T10:49:16.976724+00:00
-- url     : https://prove2.me/theorems/39e6bcfb-deb0-4f46-9c55-b59ca1e3802e
-- title:
--   Theorem A.5.3.1 — Vitali-type covering theorem for translates of a D-sequence in a locally compact abelian group
-- statement:
--   **Covering theorem for D-sequences (Hewitt–Ross), a Vitali covering lemma on locally compact abelian groups.** Let $G$ be a Hausdorff locally compact abelian group with a Haar measure $\mu_G$. A sequence $(U_k)_{k\ge0}$ of $\mu_G$-measurable subsets of $G$ containing the neutral element is a **D-sequence** with structural constant $C>0$ if for all $k\ge 0$: $0<\mu_G(U_k)<\infty$, $U_{k+1}\subset U_k$, and $0<\mu_G(U_kU_k^{-1})<C\,\mu_G(U_k)$. It is a **D′-sequence** if moreover every neighbourhood of the neutral element contains some $U_k$.
--
--   Let $(U_k)_{k\ge 0}$ be a D-sequence in $G$ with structural constant $C$, and let $\mathcal F'$ be a family of subsets of $G$ (in the source: a sub-family of the family $\mathcal F$ of all translates $xU_k$, $x\in G$, $k\ge0$). Let $B\subset G$ be a non-empty subset such that
--
--   1. $\mu_G(B\cdot U_0)<\infty$;
--   2. for each $x\in B$ there is an integer $k\ge 0$ with $xU_k\in\mathcal F'$.
--
--   Then there are finitely many pairs $(x_1,k_1),\dots,(x_N,k_N)$ with $x_i\in B$ and $x_iU_{k_i}\in\mathcal F'$ for all $i$, such that the sets $x_iU_{k_i}$ are pairwise disjoint and
--   $$\sum_{1\le i\le N}\mu_G(U_{k_i})\;>\;\frac{\mu_G(B)}{C} .$$
--
--   Here $\mu_G(B)$ and $\mu_G(B\cdot U_0)$ denote outer measures; $B$ is not assumed measurable.
--
--   This is the substitute for the Vitali covering lemma on which the maximal theorems for Radon measures and for locally integrable functions on $G$ rest (Theorems A.5.3.4–A.5.3.7 of the source), which the source applies to idele groups and idele class groups.
--
--   **Deviation from the source.** The source does not require $B\ne\varnothing$; for $B=\varnothing$ the conclusion would read $0>0$, so non-emptiness is assumed. The source assumes $B$ to be $\mu_G$-measurable while remarking (Remark A.5.3.2) that the original theorem does not and reads the measures of $B$ and $B\cdot U_0$ as outer measures; the statement follows the original.
--
--   **Formalization Note.** D-sequences are the platform notion `MasulloGRH.IsDSequence μ U C`. The measure of an arbitrary set in Mathlib is its outer measure. The selected translates are indexed by a `Finset` of pairs $(x,k)\in G\times\mathbb N$, and disjointness is `Set.PairwiseDisjoint` of the sets `x • U k`. The family `F'` is an arbitrary set of subsets of $G$; only its members of the form $xU_k$ matter.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, pp. 578-579, Theorem A.5.3.1, eq. (A.5.3.1), and Remark A.5.3.2; classical reference: E. Hewitt and K. A. Ross, Abstract Harmonic Analysis, Vol. II, Springer-Verlag, 1970, Ch. XI, Thm. 44.11, p. 638 (as cited by the paper)

import Mathlib
import Definitions.Def_MasulloGRH_DSequences

open MeasureTheory Metric Filter Topology Pointwise
open scoped ENNReal NNReal

set_option autoImplicit false

namespace MasulloGRH

theorem dSequence_vitali_covering
    {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] (U : ℕ → Set G) (C : ℝ) (hU : IsDSequence μ U C)
    (F' : Set (Set G)) (B : Set G) (hB : B.Nonempty) (hBU : μ (B * U 0) < ⊤)
    (hcover : ∀ x ∈ B, ∃ k, x • U k ∈ F') :
    ∃ s : Finset (G × ℕ), (∀ a ∈ s, a.1 ∈ B ∧ a.1 • U a.2 ∈ F') ∧
      (↑s : Set (G × ℕ)).PairwiseDisjoint (fun a => a.1 • U a.2) ∧
      μ B / ENNReal.ofReal C < ∑ a ∈ s, μ (U a.2) := by sorry

end MasulloGRH
