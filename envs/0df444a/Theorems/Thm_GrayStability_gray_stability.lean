-- Prove2me | Theorems.Thm_GrayStability_gray_stability
-- name    : GrayStability.gray_stability
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-05T21:46:37.144717+00:00
-- url     : https://prove2.me/theorems/f285b413-c44c-44f9-8a06-8f39f241967e
-- title:
--   Gray stability (Theorem 2.20): contact structures on closed manifolds have no deformations
-- statement:
--   Let $F:\mathbb{R}^n\to\mathbb{R}^c$ be smooth with $M=F^{-1}(0)$ compact and $DF$ surjective along $M$, and let $\alpha_t$, $t\in[0,1]$, be a smooth family of contact forms on $M$, with contact structures $\xi_t=\ker\alpha_t$. Then there is an isotopy $\psi_t$ of $M$ such that
--   $$T\psi_t(\xi_0)=\xi_t\qquad\text{for each } t\in[0,1],$$
--   that is, for every $y\in M$ and $v\in T_yM$: $\alpha_0(v)=0$ if and only if $\alpha_t(D\psi_t(y)v)=0$.
--
--   Gray's theorem says that contact structures on closed manifolds have discrete moduli: a smooth deformation of a contact structure is induced by an isotopy.
--
--   **Formalization Note** Geiges states the theorem on an abstract closed manifold. Here $M$ is a compact regular level set in $\mathbb{R}^n$, a special case covering every closed manifold with trivial normal bundle in some $\mathbb{R}^n$ (all spheres, all star-shaped hypersurfaces). Contact structures are cooriented, given by the global forms $\alpha_t$, as in Geiges' standing assumption.
-- source:
--   Geiges, Contact geometry, Handbook of Differential Geometry Vol. II (2006) 315-382, https://arxiv.org/abs/math/0307242, Theorem 2.20, p. 14

import Definitions.Def_GrayStability_Basic

namespace GrayStability

/-- Gray stability (Geiges, Theorem 2.20): for a smooth family of contact structures
`ξ_t = ker α_t`, `t ∈ [0, 1]`, on a closed submanifold `M ⊂ ℝⁿ` there is an isotopy
`ψ_t` of `M` with `Tψ_t(ξ_0) = ξ_t`. -/
theorem gray_stability {n c : ℕ} (F : E n → (Fin c → ℝ))
    (hF : IsCompactRegularLevel F) (α : ℝ → OneForm n) (hα : IsContactFamilyOn F α) :
    ∃ ψ : ℝ → E n → E n, IsIsotopyOf F ψ ∧
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ levelSet F, ∀ v ∈ tangentSpace F y,
        (α 0 y v = 0 ↔ pullback (ψ t) (α t) y v = 0) := by sorry

end GrayStability
