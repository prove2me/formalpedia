-- Prove2me | Theorems.Thm_MasulloGRH_isStructuralPair_annihilator
-- name    : MasulloGRH.isStructuralPair_annihilator
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T15:23:03.031846+00:00
-- url     : https://prove2.me/theorems/9d62147e-b89a-492e-83cb-bbef0dd5c457
-- title:
--   Lemma D.1.5.2(2) — duality of structural pairs: if $(\Gamma,k)$ is structural for $G$ then $(k^\perp,\Gamma^\perp)$ is structural for $\widehat G$
-- statement:
--   **Duality of structural pairs** (Lemma D.1.5.2(2)).
--
--   Let $G$ be a Hausdorff locally compact abelian group with Pontryagin dual $\widehat G$, and for a subgroup $H\subseteq G$ let $H^\perp=\{\chi\in\widehat G:\ \chi(x)=1\ \text{for all }x\in H\}$ be its annihilator, a closed subgroup of $\widehat G$. A closed subgroup $k\subseteq G$ is **good** if $k^\perp$ is open and compactly generated in $\widehat G$; a pair $(\Gamma,k)$ of subgroups of $G$ is **structural** if $\Gamma$ is open and compactly generated, $k$ is good and $k\subseteq\Gamma$. The same definitions apply to the locally compact abelian group $\widehat G$, whose dual is $G$ by Pontryagin duality.
--
--   **Statement.** If $(\Gamma,k)$ is a structural pair of $G$, then
--   $$(k^\perp,\ \Gamma^\perp)$$
--   is a structural pair of $\widehat G$: the subgroup $k^\perp\subseteq\widehat G$ is open and compactly generated, the subgroup $\Gamma^\perp\subseteq\widehat G$ is good (it is compact, and its annihilator in $\widehat{\widehat G}\cong G$ corresponds to $\Gamma$, which is open and compactly generated), and $\Gamma^\perp\subseteq k^\perp$.
--
--   Under the identification $\widehat{\Gamma/k}\cong k^\perp/\Gamma^\perp$ this is the statement that the dual of the elementary abelian Lie group $\Gamma/k\cong\mathbb R^m\times\mathbb T^n\times\mathbb Z^r\times F$ is again one of the stages of $\widehat G$. It is the group-theoretic input for the theorem that the Fourier transform maps $\mathcal S(k,\Gamma)\subseteq\mathcal S(G)$ onto $\mathcal S(\Gamma^\perp,k^\perp)\subseteq\mathcal S(\widehat G)$.
--
--   **Formalization Note.** `IsStructuralPair Γ k` is the platform predicate of `MasulloGRH_SchwartzBruhat` (open compactly generated subgroup first, good subgroup second), applied here to the group `PontryaginDual G`; goodness of $\Gamma^\perp$ therefore refers to its annihilator inside `PontryaginDual (PontryaginDual G)`. `LCAGroup.annihilator H` is $H^\perp$ as a `Subgroup (PontryaginDual G)` (definition `LCAGroup_Annihilator`).
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, pp. 760–761, Definition D.1.5.1 and Lemma D.1.5.2(2); classical reference: F. Bruhat, Distributions sur un groupe localement compact et applications à l'étude des représentations des groupes p-adiques, Bulletin de la S.M.F. 89 (1961), §9 (terminology)

import Mathlib
import Definitions.Def_MasulloGRH_SchwartzBruhat
import Definitions.Def_LCAGroup_Annihilator

open Topology

set_option autoImplicit false

namespace MasulloGRH

theorem isStructuralPair_annihilator
    (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] (Γ k : Subgroup G) (h : IsStructuralPair Γ k) :
    IsStructuralPair (LCAGroup.annihilator k) (LCAGroup.annihilator Γ) := by sorry

end MasulloGRH
