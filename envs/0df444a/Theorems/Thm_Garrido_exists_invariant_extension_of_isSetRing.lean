-- Prove2me | Theorems.Thm_Garrido_exists_invariant_extension_of_isSetRing
-- name    : Garrido.exists_invariant_extension_of_isSetRing
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-03T22:40:16.932448+00:00
-- url     : https://prove2.me/theorems/d22d7370-b961-4f77-ac1b-80b4cef68870
-- title:
--   Garrido, Theorem 2.6 for power sets — an invariant measure on an invariant ring of sets extends to an invariant measure on all subsets
-- statement:
--   Let $G$ be amenable (`Garrido.IsAmenable G`) and act on a set $X$. Let $\mathcal R$ be a ring of sets in $X$ (Mathlib's `IsSetRing`: it contains $\emptyset$ and is closed under unions and differences) with $g s \in \mathcal R$ for every $g \in G$ and $s \in \mathcal R$, and let $\mu$ assign to subsets of $X$ values in $[0, \infty]$, with $\mu(\emptyset) = 0$, $\mu(s \cup t) = \mu(s) + \mu(t)$ for disjoint $s, t \in \mathcal R$, and $\mu(g s) = \mu(s)$ for $g \in G$ and $s \in \mathcal R$. Then there is a finitely additive $\bar\mu$ on all subsets of $X$ (`IsFinitelyAdditiveMeasure`) that agrees with $\mu$ on $\mathcal R$ and is $G$-invariant (`IsInvariant G`).
--
--   Garrido writes on p. 7: “**Theorem 2.6** (Invariant Extension Theorem). *Recall Carathéodory’s Extension Theorem: If $\mathcal R$ is a subring of the boolean algebra $\mathcal A$ and $\mu$ is a measure on $\mathcal R$, then $\mu$ can be extended to a measure $\bar\mu$ on $\mathcal A$.* *If $G$ is an amenable group of automorphisms of $\mathcal A$ and $\mathcal R$, $\mu$ are $G$-invariant, then $\bar\mu$ can be chosen to be $G$-invariant.*” This is that theorem for the boolean algebra of all subsets of $X$, with no extension of $\mu$ supplied, a step between the mission's milestone [`Garrido.hasInvariantExtensionProperty_of_isAmenable`](https://prove2.me/theorems/0bf3524a-e23e-4619-abfd-96d6f28107e5), which takes an extension to all subsets as a hypothesis, and the statement for arbitrary boolean algebras. Its proof supplies that extension with [`FinitelyAdditive.exists_extension_of_isSetRing`](https://prove2.me/theorems/f5d887ac-da22-470b-b85e-ffb4d158b540).
-- source:
--   A. Garrido, "An introduction to amenable groups", lecture notes, Oxford Advanced Class in Algebra, Michaelmas 2013 (PDF, Feb 2015), p. 7, Theorem 2.6, for the boolean algebra of all subsets of a set; https://web.archive.org/web/20260805000803/https://www.math.uni-duesseldorf.de/~garrido/amenable.pdf

import Mathlib
import Definitions.Def_Garrido_Amenability

open scoped Pointwise

universe u v

namespace Garrido

theorem exists_invariant_extension_of_isSetRing {G : Type u} [Group G] (hG : IsAmenable G)
    {X : Type (max u v)} [MulAction G X] {R : Set (Set X)} (hR : MeasureTheory.IsSetRing R)
    (hRinv : ∀ (g : G), ∀ s ∈ R, g • s ∈ R) (μ : Set X → ENNReal) (h0 : μ ∅ = 0)
    (hadd : ∀ s ∈ R, ∀ t ∈ R, Disjoint s t → μ (s ∪ t) = μ s + μ t)
    (hμinv : ∀ (g : G), ∀ s ∈ R, μ (g • s) = μ s) :
    ∃ μbar : Set X → ENNReal, IsFinitelyAdditiveMeasure μbar ∧ (∀ s ∈ R, μbar s = μ s) ∧
      IsInvariant G μbar := by
  sorry

end Garrido
