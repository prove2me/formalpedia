-- Prove2me | Theorems.Thm_MasulloGRH_frechet_equiv_subspace_bidual
-- name    : MasulloGRH.frechet_equiv_subspace_bidual
-- status  : Proved
-- author  : @Ismael Correa
-- created : 2026-11-20T22:58:49.810367+00:00
-- url     : https://prove2.me/theorems/d983b29e-b5c6-441b-9fb0-ed96f1a4966d
-- title:
--   A Fréchet space is linearly homeomorphic to a subspace of its strong bidual
-- statement:
--   Let $E$ be a Fréchet space over $\mathbb C$, and let $E''=(E'_\beta)'_\beta$ be its strong bidual. Then $E$ is isomorphic, as a topological vector space, to a linear subspace of $E''$ (with the induced topology).
--
--   Indeed, a Fréchet space is metrizable and locally convex, hence bornological and in particular quasi-barrelled. For a quasi-barrelled Hausdorff locally convex space the canonical evaluation map $J\colon E\to E''$, $J(x)(f)=f(x)$, is injective (Hahn–Banach) and a topological isomorphism of $E$ onto its image $J(E)\subseteq E''$ (Schaefer IV.5.6). The statement records this as the existence of a subspace $V\subseteq E''$ and a continuous linear equivalence $E\cong V$.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix C, §C.2.4.4, proof of Lemma C.2.4.11, p. 689; H. H. Schaefer, Topological Vector Spaces, Ch. IV §5.6 (and Ch. II §8.1 for metrizable ⇒ bornological)

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

universe u

namespace MasulloGRH

theorem frechet_equiv_subspace_bidual (E : Type u) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (hE : IsFrechet E) :
    ∃ V : Submodule ℂ (StrongDual ℂ (StrongDual ℂ E)), Nonempty (E ≃L[ℂ] V) := by sorry

end MasulloGRH
