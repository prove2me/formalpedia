-- Prove2me | Theorems.Thm_MasulloGRH_isStrictLFOfNuclearFrechet_of_retract_stages
-- name    : MasulloGRH.isStrictLFOfNuclearFrechet_of_retract_stages
-- status  : Proved
-- author  : @sflicht
-- created : 2026-11-21T17:52:11.57301+00:00
-- url     : https://prove2.me/theorems/c0633dd1-7607-4562-b3de-aa1979a68e9f
-- title:
--   Retract stages give a strict LF-space of nuclear Fréchet spaces
-- statement:
--   Let $E$ be a complex vector space with a topology. Let $(F_N)_{N\ge0}$ be a sequence of nuclear Fréchet spaces with continuous linear maps $J_N\colon F_N\to E$ and $P_N\colon E\to F_N$ such that
--   $$P_N\circ J_N=\mathrm{id}_{F_N},\qquad J_N(F_N)\subseteq J_M(F_M)\ \ (N\le M),\qquad E=\bigcup_N J_N(F_N).$$
--   Assume that the topology of $E$ is the finest locally convex topology for which all the maps $J_N$ are continuous.
--
--   Then $E$ is a **strict countable inductive limit of nuclear Fréchet spaces**. The steps are $X_N=J_N(F_N)$: each, with the topology induced from $E$, is topologically isomorphic to $F_N$ (via $P_N|_{X_N}$ and $J_N$), hence nuclear Fréchet. The topology of $E$ is the inductive limit topology of the $X_N$.
--
--   This abstract form of the stage argument used for Schwartz–Bruhat spaces (Bruhat; Masullo, Appendix D, proof of Theorem D.1.5.7) applies to every space built from compatible retract stages. In particular it applies to the spaces $\mathcal S_I(G)$ of Theorem D.3.3.7.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix C, Example C.1.4.6(4), and Appendix D, proofs of Theorems D.1.5.7 and D.3.3.7

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

universe u

namespace MasulloGRH

theorem isStrictLFOfNuclearFrechet_of_retract_stages
    (E : Type u) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (F : ℕ → Type u) [∀ N, AddCommGroup (F N)] [∀ N, Module ℂ (F N)]
    [∀ N, TopologicalSpace (F N)] (hF : ∀ N, IsFrechet (F N) ∧ IsNuclear (F N))
    (J : (N : ℕ) → F N →ₗ[ℂ] E) (P : (N : ℕ) → E →ₗ[ℂ] F N)
    (hJ : ∀ N, Continuous (J N)) (hP : ∀ N, Continuous (P N))
    (hPJ : ∀ N y, P N (J N y) = y)
    (hmono : ∀ N M, N ≤ M → LinearMap.range (J N) ≤ LinearMap.range (J M))
    (hexh : ∀ x : E, ∃ N, x ∈ LinearMap.range (J N))
    (htop : ‹TopologicalSpace E› =
      sInf {t | IsLocallyConvexTopology E t ∧ ∀ N, @Continuous (F N) E _ t (J N)}) :
    IsStrictLFOfNuclearFrechet E := by
  sorry

end MasulloGRH
