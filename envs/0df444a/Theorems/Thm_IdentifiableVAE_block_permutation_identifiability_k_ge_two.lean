-- Prove2me | Theorems.Thm_IdentifiableVAE_block_permutation_identifiability_k_ge_two
-- name    : IdentifiableVAE.block_permutation_identifiability_k_ge_two
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T07:00:03.473602+00:00
-- url     : https://prove2.me/theorems/646ee1c4-f5bd-4e3d-9bd3-b1cca558115a
-- title:
--   Theorem 2 (as proved): identifiability up to $\sim_P$ for $k\ge2$
-- statement:
--   Assume the hypotheses of Theorem 1 (as stated above) and $k\ge2$. Assume further:
--
--   1. (2.i) every sufficient statistic $T_{i,j}$ is twice differentiable;
--   2. (2.ii) the mixing function $f$ has all first partial derivatives and all second cross derivatives $\partial^2f/\partial z_s\partial z_t$, $s\ne t$.
--
--   Let $\tilde\theta$ be a parameter describing a model on $U$ with the same properties: $\tilde T$ satisfies (iii) and (2.i), and $\tilde f$ satisfies (2.ii). If $p_{\tilde\theta}(x\mid u)=p_\theta(x\mid u)$ for all $u\in U$, then there are an invertible block-permutation matrix $A$ and $c\in\mathbb{R}^{nk}$ such that, for almost every $z$, $f(z)=\tilde f(\tilde z)$ for some $\tilde z$ and
--
--   $$\mathbf T(z)=A\,\tilde{\mathbf T}(\tilde z)+c.$$
--
--   Thus each block $\mathbf T_i$ is an affine image of one block $\tilde{\mathbf T}_{\sigma(i)}$,.
--
--   **Formalization Note** The conclusion concerns the matrix $A$ only. It does not say that $\tilde f^{-1}\circ f$ acts coordinatewise: when the statistics $\tilde{\mathbf T}_{\sigma(i)}$ are not injective, for example $(t^2,t^4)$, that map is not determined by the equation. The proof differentiates $\tilde{\mathbf T}$ and $\tilde f^{-1}\circ f$ twice and applies Lemma 5 to $\tilde{\mathbf T}$. The class of competing parameters $\tilde\theta$ is therefore taken to satisfy the same assumptions (iii), (2.i) and (2.ii). As in Theorem 1, the conclusion is stated almost everywhere.
-- source:
--   Khemakhem, Kingma, Monti and Hyvärinen, Variational Autoencoders and Nonlinear ICA: A Unifying Framework, AISTATS 2020, arXiv:1907.04809v4, Section 4.2, Theorem 2, p. 6; proof in Appendix B.3, eqs. (34)-(44), pp. 15-16

import Mathlib
import Definitions.Def_IdentifiableVAE_Basic

open MeasureTheory

namespace IdentifiableVAE

theorem block_permutation_identifiability_k_ge_two {n d m k : ℕ} (hk : 2 ≤ k) (hnd : n ≤ d)
    (U : Set (Fin m → ℝ)) (hU : IsOpen U)
    (Pε : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure Pε] (hPε : Pε ≪ volume)
    (θ : Param n d m k) (hθ : IsParam θ U)
    (h1 : CharFunZeroNull Pε) (h3 : SuffStatRegular θ) (h4 : HasInvertibleL θ U)
    (h21 : TwiceDiffStats θ) (h22 : HasSecondCrossPartials θ.f) :
    IdentifiableUpTo Pε U
      {θ' | IsParam θ' U ∧ SuffStatRegular θ' ∧ TwiceDiffStats θ' ∧ HasSecondCrossPartials θ'.f}
      SimPAE θ := by sorry

end IdentifiableVAE
