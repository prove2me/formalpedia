-- Prove2me | Theorems.Thm_HolomorphicMotion_iInf_dimH_inter_ball_le_dimH
-- name    : HolomorphicMotion.iInf_dimH_inter_ball_le_dimH
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-26T13:27:04.345844+00:00
-- url     : https://prove2.me/theorems/c6547982-0af6-4707-90e7-12003735480c
-- title:
--   Parameters where an analytic point enters a holomorphic motion (Shishikura, Lemma 3.2)
-- statement:
--   Let $X \subseteq \mathbb{C}$, $\lambda_0 \in \mathbb{C}$, $R > 0$, $D = \{\lambda : |\lambda - \lambda_0| < R\}$, and let $\iota_\lambda : X \to \mathbb{C}$ ($\lambda \in D$) be a holomorphic motion of $X$: $\iota_{\lambda_0} = \mathrm{id}_X$, each $\iota_\lambda$ is injective on $X$, and $\lambda \mapsto \iota_\lambda(z)$ is holomorphic on $D$ for each $z \in X$. Let $v : D \to \mathbb{C}$ be holomorphic with $v(\lambda_0) = z_0 \in X$, and assume $v(\lambda) \ne \iota_\lambda(z_0)$ for some $\lambda \in D$. Then
--
--   $$\dim_H \{\lambda \in D : v(\lambda) \in \iota_\lambda(X)\} \;\ge\; \lim_{r \to 0} \dim_H\big(X \cap D_r(z_0)\big),$$
--
--   where $D_r(z_0)$ is the disc of radius $r$ about $z_0$.
--
--   The lemma transfers the local Hausdorff dimension of a moving set to the parameter space: the parameters at which the analytically moving point $v(\lambda)$ falls into the moving set $\iota_\lambda(X)$ form a set at least as large, in dimension, as $X$ near $z_0$.
--
--   **Formalization Note** The limit $\lim_{r\to0}$ of the non-increasing function $r \mapsto \dim_H(X \cap D_r(z_0))$ is written as an infimum over $r > 0$. The source works on the unit disc with base point $0$ (here: an arbitrary disc, by an affine change of parameter), with $X \subseteq \widehat{\mathbb{C}}$ and spherical discs; for $z_0 \in \mathbb{C}$ small spherical and Euclidean discs about $z_0$ are nested up to constant factors, so the local dimensions coincide. The condition "$v(\lambda) \not\equiv \iota_\lambda(z_0)$" is stated as the existence of one parameter where they differ.
-- source:
--   M. Shishikura, The Hausdorff dimension of the boundary of the Mandelbrot set and Julia sets, Ann. of Math. (2) 147 (1998), 225-267, https://arxiv.org/abs/math/9201282, §3 'Holomorphic motions', Lemma 3.2

import Mathlib
open Topology Set Function Filter Bornology Metric MeasureTheory

namespace HolomorphicMotion

/-- **Shishikura (1998), Lemma 3.2**: let `ι l : X → ℂ` (`l ∈ ball l₀ R`) be a holomorphic
motion of `X ⊆ ℂ` based at `l₀`, and `v` a holomorphic function on the disc with `v l₀ = z₀ ∈ X`
which does not coincide with `l ↦ ι l z₀`. Then the set of parameters `l` with `v l ∈ ι l '' X`
has Hausdorff dimension at least `lim_{r → 0} dim_H (X ∩ ball z₀ r)`. -/
theorem iInf_dimH_inter_ball_le_dimH (X : Set ℂ) (l₀ : ℂ) (R : ℝ) (ι : ℂ → ℂ → ℂ)
    (h0 : ∀ z ∈ X, ι l₀ z = z) (hinj : ∀ l ∈ ball l₀ R, InjOn (ι l) X)
    (hhol : ∀ z ∈ X, DifferentiableOn ℂ (fun l ↦ ι l z) (ball l₀ R))
    (v : ℂ → ℂ) (hv : DifferentiableOn ℂ v (ball l₀ R)) (z₀ : ℂ) (hz₀ : z₀ ∈ X)
    (hvz : v l₀ = z₀) (hne : ∃ l ∈ ball l₀ R, v l ≠ ι l z₀) :
    ⨅ r > (0 : ℝ), dimH (X ∩ ball z₀ r) ≤ dimH {l ∈ ball l₀ R | v l ∈ ι l '' X} := by sorry

end HolomorphicMotion
