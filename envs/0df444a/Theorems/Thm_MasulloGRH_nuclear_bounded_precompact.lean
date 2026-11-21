-- Prove2me | Theorems.Thm_MasulloGRH_nuclear_bounded_precompact
-- name    : MasulloGRH.nuclear_bounded_precompact
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-20T22:42:40.810796+00:00
-- url     : https://prove2.me/theorems/feb7538b-bd98-4c38-bfb4-cac272c748cd
-- title:
--   Lemma C.2.4.16(1) — bounded subsets of a nuclear space are pre-compact
-- statement:
--   Let $E$ be a nuclear Hausdorff locally convex space over $\mathbb C$. Then every bounded subset $B\subset E$ is **pre-compact**, i.e. totally bounded: for every neighbourhood $V$ of $0$ there are finitely many points $x_1,\dots,x_N\in E$ with
--
--   $$B\subset\bigcup_{i=1}^N(x_i+V).$$
--
--   Together with completeness and barrelledness this gives the Montel property of the nuclear spaces of the draft.
--
--   **Formalization Note** Pre-compactness is stated as total boundedness, which the source identifies with compactness of the closure in the completion.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix C, §C.2.4, Lemma C.2.4.16 (Nuclearity and the Approximation Property), part (1), first assertion, p. 690; pre-compactness: Definition C.1.4.2, p. 661

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

namespace MasulloGRH

open TensorProduct Topology

theorem nuclear_bounded_precompact (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (hE : IsNuclear E) (B : Set E) (hB : Bornology.IsVonNBounded ℂ B) :
    ∀ V ∈ 𝓝 (0 : E), ∃ t : Finset E, B ⊆ ⋃ x ∈ t, {y : E | y - x ∈ V} := by sorry

end MasulloGRH
