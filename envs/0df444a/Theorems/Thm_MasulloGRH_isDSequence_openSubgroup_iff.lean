-- Prove2me | Theorems.Thm_MasulloGRH_isDSequence_openSubgroup_iff
-- name    : MasulloGRH.isDSequence_openSubgroup_iff
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T15:23:20.957768+00:00
-- url     : https://prove2.me/theorems/82b5fbae-b4a7-4889-bf36-ebd9d2b378e2
-- title:
--   Proposition A.5.2.3(2) — a sequence of subsets of an open subgroup $H\subset G$ is a D-sequence (resp. D′-sequence, open, symmetric) for $H$ iff it is one for $G$
-- statement:
--   **D-sequences and D′-sequences in open subgroups.** Let $G$ be a Hausdorff locally compact abelian group with a Haar measure $\lambda$. A sequence $(U_k)_{k\ge0}$ of $\lambda$-measurable subsets of $G$ containing the neutral element is a **D-sequence** in $G$ with structural constant $C>0$ if for all $k\ge 0$: $0<\lambda(U_k)<\infty$, $U_{k+1}\subset U_k$, and $$0<\lambda(U_kU_k^{-1})<C\,\lambda(U_k).$$ It is a **D′-sequence** if moreover every neighbourhood of the neutral element contains some $U_k$. A D-sequence is called open, respectively symmetric, if every $U_k$ is open, respectively satisfies $U_k^{-1}=U_k$.
--
--   Let $G$ be a Hausdorff locally compact abelian group, $\mu_G$ a Haar measure on $G$, and $H\subset G$ an open subgroup, with the Haar measure $\mu_H=\mu_G|_H$ obtained by restricting $\mu_G$ to the Borel subsets of $H$. Let $(U_k)_{k\ge0}$ be a sequence of subsets of $H$ and $C$ a real number. Then:
--
--   1. $(U_k)$ is a D-sequence in $H$ with structural constant $C$ (for $\mu_H$) if and only if it is a D-sequence in $G$ with structural constant $C$ (for $\mu_G$);
--   2. $(U_k)$ is a D′-sequence in $H$ with structural constant $C$ if and only if it is a D′-sequence in $G$ with structural constant $C$;
--   3. every $U_k$ is open in $H$ if and only if every $U_k$ is open in $G$;
--   4. every $U_k$ is symmetric in $H$ if and only if every $U_k$ is symmetric in $G$.
--
--   D′-sequences are the differentiation bases of the maximal theorem and of the version of Lebesgue's differentiation theorem of §A.5.3–A.5.4 of the source; the source combines the present statement with Proposition A.5.2.3(1) and Lemma A.5.2.5 (products) in its constructions of D′-sequences on idele groups in §A.5.2.
--
--   **Formalization Note.** $H$ is a `Subgroup G` with `IsOpen (H : Set G)`, carrying the subspace topology and the induced (Borel) measurable structure; the sequence is `U : ℕ → Set H`, its image in $G$ is `fun k => Subtype.val '' U k`, and $\mu_H$ is `μ.comap Subtype.val`, for which $\mu_H(A)=\mu_G(A)$ for every $A\subset H$. The notions are the platform's `MasulloGRH.IsDSequence` and `MasulloGRH.IsDPrimeSequence`, which carry the structural constant $C$ explicitly; the same constant appears on both sides. In the source "for $H$" refers to an arbitrary Haar measure on $H$; all conditions are invariant under rescaling the measure, and the proof in the source uses $\mu_G|_H$, as here.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 570, Proposition A.5.2.3(2) (with Definition A.5.2.1, p. 569)

import Mathlib
import Definitions.Def_MasulloGRH_DSequences

open MeasureTheory Metric Filter Topology Pointwise
open scoped ENNReal NNReal

set_option autoImplicit false

namespace MasulloGRH

theorem isDSequence_openSubgroup_iff
    {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] (H : Subgroup G) (hH : IsOpen (H : Set G))
    (U : ℕ → Set H) (C : ℝ) :
    (IsDSequence (μ.comap (Subtype.val : H → G)) U C ↔
        IsDSequence μ (fun k => Subtype.val '' U k) C) ∧
      (IsDPrimeSequence (μ.comap (Subtype.val : H → G)) U C ↔
        IsDPrimeSequence μ (fun k => Subtype.val '' U k) C) ∧
      ((∀ k, IsOpen (U k)) ↔ ∀ k, IsOpen (Subtype.val '' U k : Set G)) ∧
      ((∀ k, (U k)⁻¹ = U k) ↔
        ∀ k, (Subtype.val '' U k : Set G)⁻¹ = Subtype.val '' U k) := by sorry

end MasulloGRH
