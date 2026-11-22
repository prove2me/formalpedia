-- Prove2me | Theorems.Thm_LCAGroup_locallyEuclidean_equiv_real_torus_discrete
-- name    : LCAGroup.locallyEuclidean_equiv_real_torus_discrete
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T15:22:21.685807+00:00
-- url     : https://prove2.me/theorems/732bd652-9434-4828-8786-4bcff112dc98
-- title:
--   Theorem D.1.4.2 — a locally Euclidean Hausdorff locally compact abelian group is isomorphic to $\mathbb R^m\times\mathbb T^n\times D$ with $D$ discrete
-- statement:
--   **Structure of locally Euclidean locally compact abelian groups** (Theorem D.1.4.2 of the source).
--
--   Let $G$ be a Hausdorff locally compact abelian group which is locally Euclidean as a topological space: every point of $G$ (equivalently, by homogeneity, the identity) has an open neighbourhood homeomorphic to an open subset of $\mathbb R^N$ for some $N\ge 0$. Then there exist integers $m,n\ge 0$, a discrete abelian group $D$, and an isomorphism of topological groups
--   $$G\ \xrightarrow{\ \simeq\ }\ \mathbb R^m\times\mathbb T^n\times D\qquad\text{(D.1.4.1)},$$
--   where $\mathbb T=\mathbb R/\mathbb Z$ is the circle group.
--
--   This is the abelian case of Hilbert's fifth problem together with the classification of abelian Lie groups: the locally Euclidean locally compact abelian groups are exactly the abelian Lie groups. In the source it is the foundation of the structure theory of §D.1.4 (Theorem D.1.4.3, Lemmas D.1.4.4 and D.1.4.7), which reduces the definition of the Schwartz–Bruhat space $\mathcal S(G)$ of a general locally compact abelian group to the elementary groups $\mathbb R^m\times\mathbb T^n\times\mathbb Z^k\times F$.
--
--   **Formalization Note.** 'Locally Euclidean' is expressed without a new definition: there are $n$ and an `OpenPartialHomeomorph` (a homeomorphism between an open subset of the group and an open subset of `EuclideanSpace ℝ (Fin n)`) whose source contains the identity. For a topological group this is equivalent, by translation, to every point having a neighbourhood homeomorphic to an open subset of $\mathbb R^n$. The group $G$ is written multiplicatively, so the target is `Multiplicative ((Fin m → ℝ) × (Fin n → UnitAddCircle) × D)`, the additive group $\mathbb R^m\times(\mathbb R/\mathbb Z)^n\times D$ regarded as a multiplicative group with the product topology; `D` is a type in the same universe as `G` carrying an additive commutative group structure and the discrete topology, and `≃ₜ*` denotes an isomorphism of topological groups (a group isomorphism that is a homeomorphism).
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 757, Theorem D.1.4.2, eq. (D.1.4.1); classical reference: A. Deitmar and S. Echterhoff, Principles of Harmonic Analysis, Second Edition, Springer, 2014, Theorem 4.2.4

import Mathlib

open Topology

set_option autoImplicit false

namespace LCAGroup

theorem locallyEuclidean_equiv_real_torus_discrete.{u}
    (G : Type u) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G]
    (hG : ∃ (n : ℕ) (e : OpenPartialHomeomorph G (EuclideanSpace ℝ (Fin n))),
      (1 : G) ∈ e.source) :
    ∃ (m n : ℕ) (D : Type u) (_ : AddCommGroup D) (_ : TopologicalSpace D)
      (_ : DiscreteTopology D),
      Nonempty (G ≃ₜ* Multiplicative ((Fin m → ℝ) × (Fin n → UnitAddCircle) × D)) := by sorry

end LCAGroup
