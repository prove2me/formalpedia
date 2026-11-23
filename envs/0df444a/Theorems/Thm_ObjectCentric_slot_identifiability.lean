-- Prove2me | Theorems.Thm_ObjectCentric_slot_identifiability
-- name    : ObjectCentric.slot_identifiability
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T19:41:52.432828+00:00
-- url     : https://prove2.me/theorems/80ae129c-7a7e-432b-87ed-6f131b17fc16
-- title:
--   Theorem 1: slot identifiability
-- statement:
--   Let $K\ge0$ and $M\ge1$, let $\mathcal Z=(\mathbb R^M)^K$ and let $\mathcal X\subseteq\mathbb R^N$. Let $\mathbf f:\mathcal Z\to\mathcal X$ be a diffeomorphism with inverse $\mathbf g$ that is compositional (Definition 1) with irreducible mechanisms (Definition 5). Suppose an inference model $\hat{\mathbf g}:\mathcal X\to\mathcal Z$ is (i) a diffeomorphism with (ii) compositional inverse $\hat{\mathbf f}=\hat{\mathbf g}^{-1}$. Then $\hat{\mathbf g}$ slot-identifies $\mathbf z=\mathbf g(\mathbf x)$. That is, for every $k\in[K]$ there are a unique $j\in[K]$ and a diffeomorphism $\mathbf h_k:\mathbb R^M\to\mathbb R^M$ such that
--
--   $$\hat{\mathbf g}(\mathbf f(\mathbf z))_j=\mathbf h_k(\mathbf z_k)\qquad\text{for all }\mathbf z\in\mathcal Z.$$
--
--   The theorem needs no distributional assumption on the latents. Structure on the generator together with an invertible, compositional model suffices to recover the objects up to permutation and slot-wise reparametrisation.
--
--   **Formalization Note** The slot dimension is assumed to satisfy $M\ge1$, which the paper takes for granted. For $M=0$ and $K\ge2$ the uniqueness of $j$ fails. Diffeomorphisms are $C^1$.
-- source:
--   Brady, Zimmermann, Sharma, Schölkopf, von Kügelgen and Brendel, Provably Learning Object-Centric Representations, ICML 2023, arXiv:2305.14229v1 (2023), Section 3, Theorem 1, p. 5; proof in Appendix A, p. 20

import Mathlib
import Definitions.Def_ObjectCentric_Basic

open MeasureTheory

namespace ObjectCentric

theorem slot_identifiability {K M N : ℕ} (hM : 0 < M) (X : Set (Obs N))
    (f : Lat K M → Obs N) (g : Obs N → Lat K M) (hf : IsDiffeoWithInv f g X)
    (hfc : IsCompositional f) (hfi : IsIrreducible f)
    (ghat : Obs N → Lat K M) (fhat : Lat K M → Obs N) (hhat : IsDiffeoWithInv fhat ghat X)
    (hfhatc : IsCompositional fhat) :
    SlotIdentifies f ghat := by sorry

end ObjectCentric
