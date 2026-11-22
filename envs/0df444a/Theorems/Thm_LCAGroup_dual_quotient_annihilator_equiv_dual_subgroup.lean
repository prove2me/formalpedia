-- Prove2me | Theorems.Thm_LCAGroup_dual_quotient_annihilator_equiv_dual_subgroup
-- name    : LCAGroup.dual_quotient_annihilator_equiv_dual_subgroup
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T10:50:57.02232+00:00
-- url     : https://prove2.me/theorems/a016c464-5eda-4379-9cfd-b172b7050009
-- title:
--   Lemma D.1.4.6(2) — the dual of a closed subgroup: restriction of characters induces $\widehat G/H^\perp\cong\widehat H$ as topological groups
-- statement:
--   **Duality between closed subgroups and quotients of the dual** (Lemma D.1.4.6(2) of the source, second isomorphism).
--
--   Let $G$ be a Hausdorff locally compact abelian group with Pontryagin dual $\widehat G$, let $H\subseteq G$ be a closed subgroup (with the subspace topology), and let
--   $$H^\perp=\{\chi\in\widehat G:\ \chi(h)=1\text{ for all }h\in H\}$$
--   be its annihilator. Restriction of characters $\chi\mapsto\chi|_H$ is a continuous homomorphism $\widehat G\to\widehat H$ with kernel $H^\perp$. The lemma states that the induced map
--   $$\widehat G/H^\perp\xrightarrow{\ \sim\ }\widehat H,\qquad \chi H^\perp\longmapsto\chi|_H,$$
--   is an isomorphism of topological groups, where $\widehat G/H^\perp$ carries the quotient topology.
--
--   Equivalently: every continuous character of the closed subgroup $H$ extends to a continuous character of $G$ (surjectivity), and the restriction map $\widehat G\to\widehat H$ is open. Together with $\widehat{G/H}\cong H^\perp$ and $H^{\perp\perp}=H$ this is the duality between closed subgroups and quotients of locally compact abelian groups, used in the source for the structure theory of §D.1.4 (for instance: $H$ open in $G$ $\Rightarrow$ $H^\perp$ compact, and the description of $G$ as an inverse limit of the duals of the open compactly generated subgroups of $\widehat G$).
--
--   **Formalization Note.** `LCAGroup.annihilator H` (definition `LCAGroup_Annihilator`) is $H^\perp$ as a `Subgroup (PontryaginDual G)`, and `PontryaginDual G ⧸ LCAGroup.annihilator H` is the quotient topological group. The statement asserts the existence of a `ContinuousMulEquiv` $e\colon\widehat G/H^\perp\simeq_{t*}\widehat H$ with $e(\chi H^\perp)(x)=\chi(x)$ for all $\chi\in\widehat G$ and $x\in H$; this equation says that $e$ is induced by restriction, and the type of $e$ encodes bijectivity, multiplicativity and bicontinuity. Groups are written multiplicatively.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 758, Definition D.1.4.5 and Lemma D.1.4.6(2); classical reference: A. Deitmar and S. Echterhoff, Principles of Harmonic Analysis, Second Edition, Springer, 2014, Proposition 3.6.1

import Mathlib
import Definitions.Def_LCAGroup_Annihilator

open Topology

set_option autoImplicit false

namespace LCAGroup

theorem dual_quotient_annihilator_equiv_dual_subgroup
    (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G]
    (H : Subgroup G) (hH : IsClosed (H : Set G)) :
    ∃ e : (PontryaginDual G ⧸ annihilator H) ≃ₜ* PontryaginDual H,
      ∀ (χ : PontryaginDual G) (x : H),
        e (χ : PontryaginDual G ⧸ annihilator H) x = χ (x : G) := by sorry

end LCAGroup
