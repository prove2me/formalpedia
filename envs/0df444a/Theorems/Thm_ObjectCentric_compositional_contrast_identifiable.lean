-- Prove2me | Theorems.Thm_ObjectCentric_compositional_contrast_identifiable
-- name    : ObjectCentric.compositional_contrast_identifiable
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T19:42:50.795916+00:00
-- url     : https://prove2.me/theorems/d58b18bf-15b3-4f1e-9e24-e8185fdcc837
-- title:
--   Theorem 2: zero reconstruction error and zero compositional contrast give slot identifiability
-- statement:
--   Let $K\ge0$ and $M\ge1$, let $\mathcal Z=(\mathbb R^M)^K$ and let $\mathcal X\subseteq\mathbb R^N$. Let $\mathbf f:\mathcal Z\to\mathcal X$ be a diffeomorphism with inverse $\mathbf g$ that is compositional with irreducible mechanisms. Let the latent law $p_{\mathbf z}$ be a probability measure with full support on $\mathcal Z$ (every nonempty open set has positive mass), and let $p_{\mathbf x}=\mathbf f_*p_{\mathbf z}$. Let the encoder $\hat{\mathbf g}:\mathcal X\to\mathcal Z$ and the decoder $\hat{\mathbf f}:\mathcal Z\to\mathcal X$ be differentiable, and let $\lambda>0$. If
--
--   $$\mathbb E_{\mathbf x\sim p_{\mathbf x}}\Big[\big\|\hat{\mathbf f}(\hat{\mathbf g}(\mathbf x))-\mathbf x\big\|_2^2+\lambda\,C_{\mathrm{comp}}\big(\hat{\mathbf f},\hat{\mathbf g}(\mathbf x)\big)\Big]=0,$$
--
--   then $\hat{\mathbf g}$ slot-identifies $\mathbf z$ in the sense of Definition 6.
--
--   This is the optimisation form of Theorem 1: an auto-encoder with zero reconstruction error and zero compositional contrast identifies the objects.
--
--   **Formalization Note** Differentiable means $C^1$ here ($\hat{\mathbf g}$ relative to $\mathcal X$). The decoder's codomain $\mathcal X$ is the hypothesis $\hat{\mathbf f}(\mathcal Z)\subseteq\mathcal X$. Full support of $p_{\mathbf z}$ is the standing assumption of Section 2. The expectation is the $[0,\infty]$-valued integral over $\mathbf z\sim p_{\mathbf z}$ of the integrand at $\mathbf x=\mathbf f(\mathbf z)$, so a non-integrable integrand cannot make it vanish. The slot dimension is assumed to satisfy $M\ge1$.
-- source:
--   Brady, Zimmermann, Sharma, Schölkopf, von Kügelgen and Brendel, Provably Learning Object-Centric Representations, ICML 2023, arXiv:2305.14229v1 (2023), Section 3, Theorem 2, eq. (7), p. 6; proof in Appendix A, p. 21

import Mathlib
import Definitions.Def_ObjectCentric_Basic

open MeasureTheory

namespace ObjectCentric

theorem compositional_contrast_identifiable {K M N : ℕ} (hM : 0 < M) (X : Set (Obs N))
    (f : Lat K M → Obs N) (g : Obs N → Lat K M) (hf : IsDiffeoWithInv f g X)
    (hfc : IsCompositional f) (hfi : IsIrreducible f)
    (pz : Measure (Lat K M)) [IsProbabilityMeasure pz] [pz.IsOpenPosMeasure]
    (ghat : Obs N → Lat K M) (fhat : Lat K M → Obs N)
    (hghat : ContDiffOn ℝ 1 ghat X) (hfhat : ContDiff ℝ 1 fhat) (hfhatX : Set.range fhat ⊆ X)
    (lam : ℝ) (hlam : 0 < lam) (hobj : aeObjective f pz ghat fhat lam = 0) :
    SlotIdentifies f ghat := by sorry

end ObjectCentric
