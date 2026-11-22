-- Prove2me | Theorems.Thm_MasulloGRH_isDSequence_prod
-- name    : MasulloGRH.isDSequence_prod
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T15:23:20.053441+00:00
-- url     : https://prove2.me/theorems/5b1536a9-13fc-40b1-9d65-774cc8e4c0c4
-- title:
--   Lemma A.5.2.5 — termwise products $(U_k\times U'_k)$ of D-sequences (resp. D′-sequences) are D-sequences (resp. D′-sequences) for $\mu_1\otimes\mu_2$, with constant $C_1C_2$
-- statement:
--   **Products of D-sequences and of D′-sequences.** Let $G$ be a Hausdorff locally compact abelian group with a Haar measure $\lambda$. A sequence $(U_k)_{k\ge0}$ of $\lambda$-measurable subsets of $G$ containing the neutral element is a **D-sequence** in $G$ with structural constant $C>0$ if for all $k\ge 0$: $0<\lambda(U_k)<\infty$, $U_{k+1}\subset U_k$, and $$0<\lambda(U_kU_k^{-1})<C\,\lambda(U_k).$$ It is a **D′-sequence** if moreover every neighbourhood of the neutral element contains some $U_k$. A D-sequence is called open, respectively symmetric, if every $U_k$ is open, respectively satisfies $U_k^{-1}=U_k$.
--
--   Let $G_1,G_2$ be Hausdorff locally compact abelian groups, assumed second countable, with Haar measures $\mu_1$ on $G_1$ and $\mu_2$ on $G_2$, and let $G=G_1\times G_2$ be the product topological group with the product Haar measure $\mu=\mu_1\otimes\mu_2$. Let $(U_k)_{k\ge0}$ be a sequence of subsets of $G_1$ and $(U'_k)_{k\ge0}$ a sequence of subsets of $G_2$, and let $C_1,C_2$ be real numbers. Then:
--
--   1. if $(U_k)$ is a D-sequence in $G_1$ with structural constant $C_1$ and $(U'_k)$ is a D-sequence in $G_2$ with structural constant $C_2$, then $(U_k\times U'_k)_{k\ge0}$ is a D-sequence in $G$ with structural constant $C_1C_2$; in particular
--   $$0<\mu\big((U_k\times U'_k)(U_k\times U'_k)^{-1}\big)<C_1C_2\,\mu(U_k\times U'_k)\qquad\text{for all }k\ge0;$$
--   2. the same holds with "D′-sequence" in place of "D-sequence" throughout;
--   3. for each $k$, if $U_k$ and $U'_k$ are open then $U_k\times U'_k$ is open, and if $U_k$ and $U'_k$ are symmetric then so is $U_k\times U'_k$.
--
--   D′-sequences are the differentiation bases of the maximal theorem and of the version of Lebesgue's differentiation theorem of §A.5.3–A.5.4 of the source. The source uses the lemma in its constructions of D′-sequences on idele groups from product decompositions (§A.5.2), and in Chapter 12, where for a D′-sequence $(U_k)$ in $G$ the sequence $(U_k\times U_k)$ in $G\times G$ is used to regularize locally integrable functions on $G\times G$.
--
--   **Deviation from the source.** The source does not assume second countability. It is added here so that the product Haar measure is Mathlib's product measure `μ₁.prod μ₂` (the Haar measures are then $\sigma$-finite) and the product $\sigma$-algebra on $G_1\times G_2$ is its Borel $\sigma$-algebra; all groups to which the source applies the lemma are second countable. The source does not name the structural constant of the product sequence; the proof gives $C_1C_2$, since $(U_k\times U'_k)(U_k\times U'_k)^{-1}=(U_kU_k^{-1})\times(U'_kU_k'^{-1})$ and $\mu(B_1\times B_2)=\mu_1(B_1)\mu_2(B_2)$.
--
--   **Formalization Note.** The notions are the platform's `MasulloGRH.IsDSequence` and `MasulloGRH.IsDPrimeSequence` (measurability means null-measurability for the given measure, and the structural constant is explicit); the product sequence is `fun k => U k ×ˢ U' k`.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 570, Lemma A.5.2.5 (with Definition A.5.2.1, p. 569)

import Mathlib
import Definitions.Def_MasulloGRH_DSequences

open MeasureTheory Metric Filter Topology Pointwise
open scoped ENNReal NNReal

set_option autoImplicit false

namespace MasulloGRH

theorem isDSequence_prod
    {G₁ G₂ : Type*} [CommGroup G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [T2Space G₁]
    [LocallyCompactSpace G₁] [SecondCountableTopology G₁] [MeasurableSpace G₁] [BorelSpace G₁]
    [CommGroup G₂] [TopologicalSpace G₂] [IsTopologicalGroup G₂] [T2Space G₂]
    [LocallyCompactSpace G₂] [SecondCountableTopology G₂] [MeasurableSpace G₂] [BorelSpace G₂]
    (μ₁ : Measure G₁) [μ₁.IsHaarMeasure] (μ₂ : Measure G₂) [μ₂.IsHaarMeasure]
    (U : ℕ → Set G₁) (U' : ℕ → Set G₂) (C₁ C₂ : ℝ) :
    (IsDSequence μ₁ U C₁ → IsDSequence μ₂ U' C₂ →
        IsDSequence (μ₁.prod μ₂) (fun k => U k ×ˢ U' k) (C₁ * C₂)) ∧
      (IsDPrimeSequence μ₁ U C₁ → IsDPrimeSequence μ₂ U' C₂ →
        IsDPrimeSequence (μ₁.prod μ₂) (fun k => U k ×ˢ U' k) (C₁ * C₂)) ∧
      (∀ k, IsOpen (U k) → IsOpen (U' k) → IsOpen (U k ×ˢ U' k)) ∧
      (∀ k, (U k)⁻¹ = U k → (U' k)⁻¹ = U' k → (U k ×ˢ U' k)⁻¹ = U k ×ˢ U' k) := by sorry

end MasulloGRH
