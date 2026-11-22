-- Prove2me | Theorems.Thm_MasulloGRH_exists_isDPrimeSequence_compact_openSubgroup
-- name    : MasulloGRH.exists_isDPrimeSequence_compact_openSubgroup
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T10:49:21.478825+00:00
-- url     : https://prove2.me/theorems/909ba4b6-46de-450d-babf-9f7f875b534a
-- title:
--   Proposition A.5.2.3(1) — a first countable totally disconnected locally compact abelian group has a D′-sequence of compact open subgroups
-- statement:
--   **Existence of D′-sequences in totally disconnected groups.** Let $G$ be a Hausdorff locally compact abelian group with a Haar measure $\mu_G$. A sequence $(U_k)_{k\ge0}$ of $\mu_G$-measurable subsets of $G$ containing the neutral element is a **D-sequence** with structural constant $C>0$ if for all $k\ge 0$: $0<\mu_G(U_k)<\infty$, $U_{k+1}\subset U_k$, and $0<\mu_G(U_kU_k^{-1})<C\,\mu_G(U_k)$. It is a **D′-sequence** if moreover every neighbourhood of the neutral element contains some $U_k$.
--
--   Let $G$ be a Hausdorff locally compact abelian group which is first countable and locally profinite, i.e. totally disconnected. Then there is a sequence $(U_k)_{k\ge 0}$ of compact open subgroups of $G$ which is a D′-sequence in $G$ with structural constant $C$, for every real number $C>1$. Thus the $U_k$ are open, symmetric ($U_k=U_k^{-1}$), decreasing, of finite positive Haar measure, they form a base of neighbourhoods of the neutral element, and $U_kU_k^{-1}=U_k$.
--
--   In the terminology of Remark A.5.2.2 of the source, $(U_k,V_k)_{k\ge0}$ with $V_k=U_k^2=U_k$ is then a D″-sequence with $C'=1$, since $V_kV_k^{-1}=U_k$ and $\mu_G(U_k)=\mu_G(V_k)$.
--
--   This provides the differentiation bases at the non-archimedean places: the source combines it with products and quotients to build D′-sequences on idele groups and idele class groups, along which the maximal theorem and Lebesgue's differentiation theorem are applied.
--
--   **Deviation from the source.** The proof in the source takes the structural constant $C=1$. This is not possible: for a subgroup $U_kU_k^{-1}=U_k$, and the doubling condition (A.5.2.1) is the strict inequality $\mu_G(U_kU_k^{-1})<C\,\mu_G(U_k)$. The statement holds, with the same sequence, for every $C>1$, and this is what is formalized.
--
--   **Formalization Note.** "Locally profinite" is `TotallyDisconnectedSpace` together with the standing Hausdorff and locally compact hypotheses. The subgroups are `OpenSubgroup G` with compact underlying sets, and the D′ property is the platform notion `MasulloGRH.IsDPrimeSequence μ (fun k => (K k : Set G)) C`. The D″ part of the source is not formalized separately (the platform has no D″ notion; it is immediate from the displayed properties).
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 570, Proposition A.5.2.3(1) (with Definition A.5.2.1 and Remark A.5.2.2, p. 569)

import Mathlib
import Definitions.Def_MasulloGRH_DSequences

open MeasureTheory Metric Filter Topology Pointwise
open scoped ENNReal NNReal

set_option autoImplicit false

namespace MasulloGRH

theorem exists_isDPrimeSequence_compact_openSubgroup
    {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [TotallyDisconnectedSpace G] [FirstCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] :
    ∃ K : ℕ → OpenSubgroup G, (∀ k, IsCompact (K k : Set G)) ∧
      ∀ C : ℝ, 1 < C → IsDPrimeSequence μ (fun k => (K k : Set G)) C := by sorry

end MasulloGRH
