-- Prove2me | Theorems.Thm_LCAGroup_dual_quotient_equiv_annihilator
-- name    : LCAGroup.dual_quotient_equiv_annihilator
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T10:50:54.287092+00:00
-- url     : https://prove2.me/theorems/92959483-8c76-417f-bfe3-218eb2e09d7d
-- title:
--   Lemma D.1.4.6(2) — the dual of a quotient is the annihilator: $\widehat{G/H}\cong H^\perp$ as topological groups
-- statement:
--   **Duality between quotients and annihilators** (Lemma D.1.4.6(2) of the source, first isomorphism).
--
--   Let $G$ be a Hausdorff locally compact abelian group with Pontryagin dual $\widehat G$, let $H\subseteq G$ be a closed subgroup with quotient map $\pi\colon G\to G/H$, and let
--   $$H^\perp=\{\chi\in\widehat G:\ \chi(h)=1\text{ for all }h\in H\}$$
--   be the annihilator of $H$, a closed subgroup of $\widehat G$ with the subspace topology. Composition with $\pi$ sends a character $\eta$ of $G/H$ to the character $\eta\circ\pi$ of $G$, which is trivial on $H$. The lemma states that
--   $$\widehat{G/H}\xrightarrow{\ \sim\ }H^\perp,\qquad \eta\longmapsto\eta\circ\pi,$$
--   is an isomorphism of topological groups (a group isomorphism and a homeomorphism for the compact-open topologies).
--
--   Together with $\widehat G/H^\perp\cong\widehat H$ and $H^{\perp\perp}=H$ this is the duality between closed subgroups and quotients of locally compact abelian groups. In the source it identifies $H^\perp$ with $\widehat{G/H}$ in the Poisson summation formula (Situation D.1.2.6), gives "$H$ compact $\Rightarrow H^\perp$ open" and "$H$ open $\Rightarrow H^\perp$ compact" (Lemma D.1.4.6(3)–(4)), and underlies the good subgroups and structural pairs used to define the Schwartz–Bruhat space $\mathcal S(G)$.
--
--   **Formalization Note.** `LCAGroup.annihilator H` (definition `LCAGroup_Annihilator`) is $H^\perp$ as a `Subgroup (PontryaginDual G)`. The statement asserts the existence of a `ContinuousMulEquiv` $e\colon\widehat{G/H}\simeq_{t*}H^\perp$ such that $e(\eta)(x)=\eta(xH)$ for all $\eta$ and all $x\in G$; this equation says that $e$ is the pull-back $\eta\mapsto\eta\circ\pi$, and the type of $e$ encodes bijectivity, multiplicativity and bicontinuity. `G ⧸ H` carries the quotient topology and groups are written multiplicatively.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 758, Definition D.1.4.5 and Lemma D.1.4.6(2); classical reference: A. Deitmar and S. Echterhoff, Principles of Harmonic Analysis, Second Edition, Springer, 2014, Proposition 3.6.1

import Mathlib
import Definitions.Def_LCAGroup_Annihilator

open Topology

set_option autoImplicit false

namespace LCAGroup

theorem dual_quotient_equiv_annihilator
    (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G]
    (H : Subgroup G) (hH : IsClosed (H : Set G)) :
    ∃ e : PontryaginDual (G ⧸ H) ≃ₜ* annihilator H,
      ∀ (η : PontryaginDual (G ⧸ H)) (x : G),
        (e η : PontryaginDual G) x = η (x : G ⧸ H) := by sorry

end LCAGroup
