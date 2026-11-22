-- Prove2me | Theorems.Thm_MasulloGRH_isGoodSubgroup_inf_and_isStructuralPair_sup_inf
-- name    : MasulloGRH.isGoodSubgroup_inf_and_isStructuralPair_sup_inf
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T15:23:01.986921+00:00
-- url     : https://prove2.me/theorems/931345e6-6ce7-4282-9e57-d16832709176
-- title:
--   Lemma D.1.5.2 — good subgroups are stable under intersection and structural pairs are directed: $(\Gamma_1\Gamma_2,\,k_1\cap k_2)$ is structural
-- statement:
--   **Directedness of the structural pairs of a locally compact abelian group** (Definition D.1.5.1, the remark following it, and the first assertion of Lemma D.1.5.2).
--
--   Let $G$ be a Hausdorff locally compact abelian group with Pontryagin dual $\widehat G$. A closed subgroup $k\subseteq G$ is **good** if its annihilator $k^\perp=\{\chi\in\widehat G:\ \chi(x)=1\ \text{for all }x\in k\}$ is an open and compactly generated subgroup of $\widehat G$. A pair $(\Gamma,k)$ of subgroups of $G$ is **structural** if $\Gamma$ is open and compactly generated, $k$ is good, and $k\subseteq\Gamma$. The structural pairs are ordered by $(\Gamma_1,k_1)\preceq(\Gamma_2,k_2)$ iff $\Gamma_1\subseteq\Gamma_2$ and $k_1\supseteq k_2$.
--
--   The statement has two parts.
--
--   1. If $k_1,k_2\subseteq G$ are good subgroups, then $k_1\cap k_2$ is a good subgroup.
--   2. If $(\Gamma_1,k_1)$ and $(\Gamma_2,k_2)$ are structural pairs, then
--   $$(\Gamma_1\Gamma_2,\ k_1\cap k_2)$$
--   is a structural pair. It dominates both: $(\Gamma_i,k_i)\preceq(\Gamma_1\Gamma_2,k_1\cap k_2)$ for $i=1,2$.
--
--   Hence the set $\mathcal F$ of structural pairs is directed (filtered) for $\preceq$. This is what makes the Schwartz–Bruhat space $\mathcal S(G)=\varinjlim_{(\Gamma,k)\in\mathcal F}\mathcal S(k,\Gamma)$ of Bruhat a directed union, and it is used in every reduction of a statement about $\mathcal S(G)$ to elementary abelian Lie groups $\Gamma/k$.
--
--   **Formalization Note.** `IsGoodSubgroup`, `IsStructuralPair` and `IsCompactlyGeneratedSubgroup` are the platform definitions of `MasulloGRH_SchwartzBruhat` (argument order `IsStructuralPair Γ k`). $\Gamma_1\Gamma_2$ is the join `Γ₁ ⊔ Γ₂` and $k_1\cap k_2$ the meet `k₁ ⊓ k₂` in the lattice of subgroups. The two domination relations are the trivial inclusions `Γᵢ ≤ Γ₁ ⊔ Γ₂` and `k₁ ⊓ k₂ ≤ kᵢ` and are not restated in Lean.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, pp. 760–761, Definition D.1.5.1 (with the remark following it) and Lemma D.1.5.2 (first assertion); classical reference: F. Bruhat, Distributions sur un groupe localement compact et applications à l'étude des représentations des groupes p-adiques, Bulletin de la S.M.F. 89 (1961), §9 (terminology)

import Mathlib
import Definitions.Def_MasulloGRH_SchwartzBruhat

open Topology

set_option autoImplicit false

namespace MasulloGRH

theorem isGoodSubgroup_inf_and_isStructuralPair_sup_inf
    (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] :
    (∀ k₁ k₂ : Subgroup G, IsGoodSubgroup k₁ → IsGoodSubgroup k₂ → IsGoodSubgroup (k₁ ⊓ k₂)) ∧
    (∀ Γ₁ k₁ Γ₂ k₂ : Subgroup G, IsStructuralPair Γ₁ k₁ → IsStructuralPair Γ₂ k₂ →
      IsStructuralPair (Γ₁ ⊔ Γ₂) (k₁ ⊓ k₂)) := by sorry

end MasulloGRH
