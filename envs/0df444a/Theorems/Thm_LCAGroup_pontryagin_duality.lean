-- Prove2me | Theorems.Thm_LCAGroup_pontryagin_duality
-- name    : LCAGroup.pontryagin_duality
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T10:49:22.971814+00:00
-- url     : https://prove2.me/theorems/0f676f52-187b-4b4c-b4d5-313d6806da42
-- title:
--   Theorem D.1.1.1(2) — Pontryagin duality: evaluation is an isomorphism of topological groups $G\cong\widehat{\widehat G}$
-- statement:
--   **Pontryagin duality theorem** (Theorem D.1.1.1(2) of the source).
--
--   Let $G$ be a Hausdorff locally compact abelian group, and let $\widehat G$ be its Pontryagin dual: the group of continuous characters $\chi\colon G\to U(1)$ with pointwise multiplication and the compact-open topology. Then $\widehat G$ is again a Hausdorff locally compact abelian group, so the double dual $\widehat{\widehat G}$ is defined. Every $g\in G$ defines a character of $\widehat G$ by evaluation,
--   $$\iota_G(g)(\chi)=\chi(g)\qquad(\chi\in\widehat G).$$
--   The theorem states that
--   $$\iota_G\colon G\xrightarrow{\ \sim\ }\widehat{\widehat G}$$
--   is an isomorphism of topological groups, i.e. a group isomorphism that is a homeomorphism.
--
--   In particular the duality pairing $G\times\widehat G\to U(1)$, $(g,\chi)\mapsto\chi(g)$, is separating: characters separate the points of $G$ (injectivity of $\iota_G$), and every continuous character of $\widehat G$ is the evaluation at a unique point of $G$ (surjectivity). This is the foundation of harmonic analysis on locally compact abelian groups (Fourier inversion, Plancherel, annihilators, structure theory). The source uses it throughout Appendix D, for groups such as the adele ring $\mathbb A_F$, the local fields $F_v$, the groups $F_v^\times$ and $\mathrm{GL}_1(\mathbb A_F)$, and the idele class group $C_F$.
--
--   **Formalization Note.** `PontryaginDual G` is Mathlib's dual group (continuous homomorphisms $G\to$ `Circle`, compact-open topology); groups are written multiplicatively. The statement asserts the existence of a `ContinuousMulEquiv` $e\colon G\simeq_{t*}\widehat{\widehat G}$ with $e(x)(\chi)=\chi(x)$ for all $x\in G$, $\chi\in\widehat G$. The displayed equation determines $e$ as the evaluation map $\iota_G$ of (D.1.1.3), and the type of $e$ encodes that $\iota_G$ is multiplicative, bijective, continuous and open.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 746, Theorem D.1.1.1(2), eqs. (D.1.1.1)–(D.1.1.3); classical reference: W. Rudin, Fourier Analysis on Groups, Wiley-Interscience, 1962, Theorem 1.7.2

import Mathlib

open Topology

set_option autoImplicit false

namespace LCAGroup

theorem pontryagin_duality
    (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] :
    ∃ e : G ≃ₜ* PontryaginDual (PontryaginDual G),
      ∀ (x : G) (χ : PontryaginDual G), e x χ = χ x := by sorry

end LCAGroup
