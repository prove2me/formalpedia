-- Prove2me | Theorems.Thm_LCAGroup_compactlyGenerated_locallyEuclidean_iff_elementary
-- name    : LCAGroup.compactlyGenerated_locallyEuclidean_iff_elementary
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T15:22:25.143914+00:00
-- url     : https://prove2.me/theorems/13fe73bd-5394-46cd-abe7-475db08cf6a4
-- title:
--   Theorem D.1.4.3(2) — $G$ is compactly generated and locally Euclidean if and only if $G\cong\mathbb R^m\times\mathbb T^n\times\mathbb Z^k\times F$ with $F$ finite abelian
-- statement:
--   **Characterization of elementary abelian Lie groups** (Theorem D.1.4.3(2) of the source).
--
--   Let $G$ be a Hausdorff locally compact abelian group. Then the following are equivalent:
--
--   1. $G$ is compactly generated (some compact neighbourhood of the identity generates $G$, Definition D.1.4.1) and locally Euclidean (the identity, equivalently every point, has an open neighbourhood homeomorphic to an open subset of some $\mathbb R^N$);
--   2. there exist integers $m,n,k\ge 0$, a finite abelian group $F$, and an isomorphism of topological groups
--   $$G\ \xrightarrow{\ \simeq\ }\ \mathbb R^m\times\mathbb T^n\times\mathbb Z^k\times F\qquad\text{(D.1.4.2)},$$
--   where $\mathbb T=\mathbb R/\mathbb Z$ and $\mathbb Z^k\times F$ carries the discrete topology.
--
--   The groups in 2 are the *elementary abelian Lie groups* of §D.1.3 of the source, on which the Schwartz–Bruhat space is defined directly by smoothness and rapid decay (Definition D.1.3.1). The theorem identifies them intrinsically; it is applied in §D.1.4.3 to the quotients $A_{ij}=G_j/K_i$ and $\Gamma/k$ (for structural pairs $(\Gamma,k)$), which is how $\mathcal S(G)$ is assembled for a general locally compact abelian group $G$.
--
--   **Formalization Note.** 'Compactly generated' (Definition D.1.4.1) is written out as `∃ U ∈ 𝓝 1, IsCompact U ∧ Subgroup.closure U = ⊤`: some compact neighbourhood of the identity generates the group. 'Locally Euclidean' is expressed without a new definition: there are $n$ and an `OpenPartialHomeomorph` (a homeomorphism between an open subset of the group and an open subset of `EuclideanSpace ℝ (Fin n)`) whose source contains the identity. For a topological group this is equivalent, by translation, to every point having a neighbourhood homeomorphic to an open subset of $\mathbb R^n$. The finite abelian group is presented as $F=\prod_{i<s}\mathbb Z/d_i\mathbb Z$ with all $d_i\neq 0$ (`ZMod (d i)`, with its discrete topology); every finite abelian group is of this form. The target `Multiplicative ((Fin m → ℝ) × (Fin n → UnitAddCircle) × (Fin k → ℤ) × ((i : Fin s) → ZMod (d i)))` is the additive group $\mathbb R^m\times(\mathbb R/\mathbb Z)^n\times\mathbb Z^k\times F$ written multiplicatively, with the product topology; this type is the same as `Multiplicative (MasulloGRH.ElemGroup m n k s d)` for the platform definition of the elementary groups (which is not imported). `≃ₜ*` is an isomorphism of topological groups.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 757, Definition D.1.4.1 and Theorem D.1.4.3(2), eq. (D.1.4.2); classical reference: A. Deitmar and S. Echterhoff, Principles of Harmonic Analysis, Second Edition, Springer, 2014, Corollaries 4.2.5 and 4.2.6

import Mathlib

open Topology

set_option autoImplicit false

namespace LCAGroup

theorem compactlyGenerated_locallyEuclidean_iff_elementary
    (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] :
    ((∃ U ∈ 𝓝 (1 : G), IsCompact U ∧ Subgroup.closure U = ⊤) ∧
      ∃ (n : ℕ) (e : OpenPartialHomeomorph G (EuclideanSpace ℝ (Fin n))), (1 : G) ∈ e.source) ↔
    ∃ (m n k s : ℕ) (d : Fin s → ℕ), (∀ i, d i ≠ 0) ∧
      Nonempty (G ≃ₜ* Multiplicative
        ((Fin m → ℝ) × (Fin n → UnitAddCircle) × (Fin k → ℤ) × ((i : Fin s) → ZMod (d i)))) := by sorry

end LCAGroup
