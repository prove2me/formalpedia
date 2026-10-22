-- Prove2me | Theorems.Thm_NewtonCartan_exists_potential_of_spatial_F
-- name    : NewtonCartan.exists_potential_of_spatial_F
-- status  : Proved
-- author  : @Ethan Cheung
-- created : 2026-10-21T06:37:33.587085+00:00
-- url     : https://prove2.me/theorems/a3c181c0-d363-4eb8-9994-66411d969ea5
-- title:
--   Spatial Poincaré lemma: integrate a spatially closed Hessian on $\mathbb{R}^4$
-- statement:
--   Let $F^a{}_d$ be smooth on $\mathbb{R}^4$ with $F^0{}_d=F^a{}_0=0$, $F^i{}_j=F^j{}_i$, and
--   $$
--   \partial_k F^i{}_j=\partial_j F^i{}_k\qquad(i,j,k\text{ spatial}).
--   $$
--   Then there exists a smooth potential $\varphi$ such that
--   $$
--   \partial_j(\nabla^i\varphi)=F^i{}_j\qquad(i,j\text{ spatial}).
--   $$
--   The construction integrates the spatial Hessian on each constant-$t$ slice (global Poincaré lemma on $\mathbb{R}^3$) and assembles the slices smoothly in $t$.
--
--   Formalization Note. Corrects the retired `exists_potential_of_closed_F`.
-- source:
--   Malament Prop. 4.2.5 Poincaré step; Schwartz Thm. 2.29

import Definitions.Def_NewtonCartan_defs

open scoped ContDiff

namespace NewtonCartan

/-- If $F^a{}_d$ is smooth, vanishes on temporal indices, is symmetric, and is closed as a Hessian in
spatial indices, then there is smooth $\varphi$ with $\partial_j\partial_i\varphi = F^i{}_j$ for spatial $i,j$
(equivalently $\partial_j(\nabla^i\varphi)=F^i{}_j$). -/
theorem exists_potential_of_spatial_F (F : E → Fin 4 → Fin 4 → ℝ)
    (hF : ContDiff ℝ ∞ F)
    (hrow : ∀ x d, F x 0 d = 0) (hcol : ∀ x a, F x a 0 = 0)
    (hsym : ∀ x i j, F x i j = F x j i)
    (hclosed : ∀ x i j k, i ≠ 0 → j ≠ 0 → k ≠ 0 →
      pd (fun y => F y i j) k x = pd (fun y => F y i k) j x) :
    ∃ φ : E → ℝ, ContDiff ℝ ∞ φ ∧
      ∀ x i j, i ≠ 0 → j ≠ 0 →
        pd (fun y => gradUp φ y i) j x = F x i j := by sorry

end NewtonCartan
