-- Prove2me | Theorems.Thm_Mandelbrot_hyperbolicSet_holomorphicMotion
-- name    : Mandelbrot.hyperbolicSet_holomorphicMotion
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-26T13:27:14.529642+00:00
-- url     : https://prove2.me/theorems/9dc3a5ec-ac82-4ecd-a8b1-5869b2f3fe56
-- title:
--   Stability of hyperbolic sets: a hyperbolic set of $z^2+c_0$ moves holomorphically
-- statement:
--   Let $f_c(z) = z^2 + c$ and let $K \subseteq \mathbb{C}$ be a hyperbolic set of $f_{c_0}$: $K$ is compact, $f_{c_0}(K) \subseteq K$, and $|(f_{c_0}^{n})'| > 1$ on $K$ for some $n \ge 1$. Then there are $\rho > 0$ and maps $\iota_c : K \to \mathbb{C}$, for $|c - c_0| < \rho$, such that
--
--   1. $\iota_{c_0} = \mathrm{id}_K$;
--   2. each $\iota_c$ is injective and continuous on $K$;
--   3. for each $z \in K$, the map $c \mapsto \iota_c(z)$ is holomorphic on the disc $|c - c_0| < \rho$;
--   4. $\iota_c$ conjugates the dynamics: $\iota_c(f_{c_0}(z)) = f_c(\iota_c(z))$ for all $z \in K$;
--   5. $K_c = \iota_c(K)$ is a hyperbolic set of $f_c$.
--
--   $$\iota_c \circ f_{c_0} = f_c \circ \iota_c \ \text{ on } K, \qquad K_c = \iota_c(K) \text{ hyperbolic for } f_c .$$
--
--   This is the structural stability of hyperbolic sets: $\{\iota_c\}$ is a holomorphic motion of $K$ compatible with the dynamics. It is the starting point of Shishikura's transfer of Hausdorff dimension from the dynamical plane to the parameter plane.
--
--   **Formalization Note** The source states the property for perturbations of a rational map in the space of rational maps of the same degree; this is its restriction to the one-parameter family $z^2 + c$. Hyperbolicity is expressed with the platform definition `Mandelbrot.IsHyperbolicSet` (Euclidean derivative of one iterate $> 1$), which for compact subsets of $\mathbb{C}$ is equivalent to the spherical condition $\|(f^n)'\| \ge C\kappa^n$ used in the source.
-- source:
--   M. Shishikura, The Hausdorff dimension of the boundary of the Mandelbrot set and Julia sets, Ann. of Math. (2) 147 (1998), 225-267, https://arxiv.org/abs/math/9201282, §1, 'Properties of hyperbolic subsets', Property (1.2)

import Definitions.Def_mandelbrot_hyperbolic_sets
open Topology Set Function Filter Bornology Metric MeasureTheory

namespace Mandelbrot

/-- **Stability of hyperbolic sets** (Shishikura 1998, §1, Property (1.2)), specialised to the
quadratic family: a hyperbolic set `K` of `z ↦ z ^ 2 + c₀` moves holomorphically, by a family of
injective, continuous conjugacies `ι c : K → ι c '' K` depending holomorphically on `c`, onto a
hyperbolic set of `z ↦ z ^ 2 + c`, for all `c` near `c₀`. -/
theorem hyperbolicSet_holomorphicMotion (c₀ : ℂ) (K : Set ℂ) (hK : IsHyperbolicSet c₀ K) :
    ∃ ρ > 0, ∃ ι : ℂ → ℂ → ℂ,
      (∀ z ∈ K, ι c₀ z = z) ∧
      (∀ c ∈ ball c₀ ρ, InjOn (ι c) K) ∧
      (∀ z ∈ K, DifferentiableOn ℂ (fun c ↦ ι c z) (ball c₀ ρ)) ∧
      (∀ c ∈ ball c₀ ρ, ContinuousOn (ι c) K) ∧
      (∀ c ∈ ball c₀ ρ, ∀ z ∈ K, ι c (z ^ 2 + c₀) = ι c z ^ 2 + c) ∧
      (∀ c ∈ ball c₀ ρ, IsHyperbolicSet c (ι c '' K)) := by sorry

end Mandelbrot
