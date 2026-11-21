-- Prove2me | Theorems.Thm_MasulloGRH_nuclear_finite_rank_dense
-- name    : MasulloGRH.nuclear_finite_rank_dense
-- status  : Proved
-- author  : @ghseeli
-- created : 2026-11-21T00:38:51.633231+00:00
-- url     : https://prove2.me/theorems/3f7fb400-91a7-49eb-a695-576ff310b42b
-- title:
--   Finite-rank tensor sums are dense for bounded convergence
-- statement:
--   Let $E,F$ be Hausdorff locally convex complex vector spaces and suppose that $E$ is nuclear. In the topology of uniform convergence on bounded subsets of $E$, the continuous linear maps of the form $$x\longmapsto\sum_{j=1}^N\varphi_j(x)y_j,\qquad \varphi_j\in E^\prime,\ y_j\in F,$$ form a dense subset of $\mathcal L(E,F)$. Equivalently, the image of the algebraic tensor map $E^\prime\otimes F\to\mathcal L_\beta(E,F)$ is dense. No completeness or countability assumption is imposed.
--
--   This is Remark C.2.4.17. Taking $F=E$ gives the bounded-convergence version of the approximation-property assertion in Lemma C.2.4.16(2).
--
--   Formalization Note: this statement uses actual topological density. Mathlib equips the continuous-linear-map space with its bounded-convergence topology. The dense subset is written as explicit finite sums of rank-one maps; the topological additive-group instance on the target makes this operator topology available in the theorem type.
-- source:
--   A. M. Masullo, The Music of the Primes, frozen 20 November 2026 draft, p. 690, Remark C.2.4.17, with Lemma C.2.4.16(2) as the identity-map special case. https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf. This is the actual density statement in the bounded-convergence operator topology, with the image of the algebraic tensor map represented by its explicit finite rank-one sums.

import Definitions.Def_MasulloGRH_LocallyConvex
set_option autoImplicit false
open MasulloGRH Filter Topology Set
open scoped BigOperators

theorem MasulloGRH.nuclear_finite_rank_dense (E F : Type*) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
    (hE : IsNuclear E) (hF : IsHLCS F) :
    Dense {T : E →L[ℂ] F | ∃ (N : ℕ) (φ : Fin N → StrongDual ℂ E) (y : Fin N → F),
      ∀ x, T x = ∑ i, φ i x • y i} := by sorry
