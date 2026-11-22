-- Prove2me | Theorems.Thm_MasulloGRH_isFrechet_and_isNuclear_of_countable_projective
-- name    : MasulloGRH.isFrechet_and_isNuclear_of_countable_projective
-- status  : Proved
-- author  : @sflicht
-- created : 2026-11-21T17:57:57.431068+00:00
-- url     : https://prove2.me/theorems/9df1cd4a-993a-4cb8-8814-df514af65124
-- title:
--   Countable projective limits of nuclear Fréchet spaces with closed image
-- statement:
--   Let $(Y_i)_{i\in\iota}$ be a non-empty countable family of nuclear Fréchet spaces over $\mathbb C$. Let $E$ be a complex vector space with linear maps $\pi_i\colon E\to Y_i$. Assume:
--   - $E$ carries the projective topology, i.e. the coarsest topology making all $\pi_i$ continuous;
--   - the $\pi_i$ jointly separate points: if $\pi_i(x)=0$ for all $i$, then $x=0$;
--   - the image of the diagonal map
--   $$\Phi\colon E\to\prod_{i\in\iota}Y_i,\qquad x\mapsto(\pi_i x)_i$$
--   is closed.
--
--   Then $E$ is a nuclear Fréchet space.
--
--   In Masullo's Appendix D, the spaces $\mathcal S_I(k,G)$ of Definition D.3.3.3 carry the projective topology of the weights $T_a\colon\phi\mapsto|\cdot|_G^a\phi$, $a\in I$. It can be defined by countably many $a_j\in I$, with values in nuclear Fréchet Schwartz–Bruhat spaces. This lemma is the general principle that makes each such stage a nuclear Fréchet space (proof of Theorem D.3.3.7).
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix C (Lemma C.2.4.10, permanence of nuclearity) and Appendix D, proof of Theorem D.3.3.7; standard (Trèves, Topological Vector Spaces, Distributions and Kernels, Prop. 50.1)

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

universe u

namespace MasulloGRH

theorem isFrechet_and_isNuclear_of_countable_projective (ι : Type u) [Countable ι] [Nonempty ι] (Y : ι → Type u)
    [∀ i, AddCommGroup (Y i)] [∀ i, Module ℂ (Y i)] [∀ i, TopologicalSpace (Y i)]
    (hY : ∀ i, IsFrechet (Y i) ∧ IsNuclear (Y i))
    (E : Type u) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (π : ∀ i, E →ₗ[ℂ] Y i)
    (htop : ‹TopologicalSpace E› = ⨅ i, TopologicalSpace.induced (π i) inferInstance)
    (hsep : ∀ x : E, (∀ i, π i x = 0) → x = 0)
    (hclosed : IsClosed (Set.range fun x : E => fun i => π i x)) :
    IsFrechet E ∧ IsNuclear E := by
  sorry

end MasulloGRH
