-- Prove2me | Theorems.Thm_KontsevichHMS_torus_fukaya_category_exists
-- name    : KontsevichHMS.torus_fukaya_category_exists
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-15T03:04:35.430977+00:00
-- url     : https://prove2.me/theorems/b6040c9a-8fb5-4cd8-85da-1105edf7ee22
-- title:
--   Fukaya's $A_\infty$-category of the flat two-torus exists
-- statement:
--   Kontsevich's A-side is Fukaya's $A_\infty$-category: objects are Lagrangian submanifolds with graded lifts and unitary local systems, $\mathrm{Hom}(L_1,L_2)$ is spanned by the intersection points and graded by the Maslov index, and the compositions count pseudo-holomorphic discs weighted by $\exp(-\mathrm{area})$ and by holonomy (pp. 16--17). For the flat two-torus the discs are the triangles of the last section, and the construction becomes elementary.
--
--   The milestone asks for that construction: for every total area there exists a strictly unital $A_\infty$-category over $\mathbb{C}$ together with an assignment of an object to every graded brane, such that for transverse branes the Floer space $\mathbb{C}^{L_1 \cap L_2}$ embeds linearly onto $\mathrm{Hom}^{\mu(b_1,b_2)}$, all other graded pieces vanish, and $m_2$ on the basis vectors is given by Kontsevich's structure constants $c(p,q,r)$. Nothing is prescribed about the higher products $m_{\ge 3}$ beyond the $A_\infty$ axioms, and nothing is prescribed for pairs of parallel branes.
-- source:
--   M. Kontsevich, Homological algebra of mirror symmetry, Proc. ICM Zurich 1994, arXiv:alg-geom/9411018, pp. 16-17 (Fukaya's A-infinity-category) specialised to pp. 18-19 (the flat two-torus)

import Mathlib
import Definitions.Def_KontsevichHMS_AInfCategory
import Definitions.Def_KontsevichHMS_TorusBrane

namespace KontsevichHMS

open Brane

/-- **Fukaya's construction for the flat two-torus.**  There is a strictly unital
A∞-category over `ℂ` whose objects include the graded branes, whose morphism space between
two transverse branes is the Floer space spanned by their intersection points, placed in the
degree given by the Maslov index, and whose product `m₂` is given by Kontsevich's
triangle counts. -/
theorem torus_fukaya_category_exists (area : ℝ) (harea : 0 < area) :
    ∃ (C : AInfCategory.{0} ℂ) (ι : Brane → C.Obj) (e : C.Obj → C.A)
      (ψ : ∀ b₁ b₂ : Brane, (↥(isect b₁ b₂) →₀ ℂ) →ₗ[ℂ] C.A),
      C.IsStrictlyUnital e ∧
      (∀ b₁ b₂ : Brane, Transverse b₁ b₂ →
        Function.Injective (ψ b₁ b₂) ∧
          LinearMap.range (ψ b₁ b₂) = C.homDeg (ι b₁) (ι b₂) (maslov b₁ b₂)) ∧
      (∀ b₁ b₂ : Brane, Transverse b₁ b₂ → ∀ d : ℤ, d ≠ maslov b₁ b₂ →
        C.homDeg (ι b₁) (ι b₂) d = ⊥) ∧
      (∀ b₁ b₂ b₃ : Brane, Transverse b₁ b₂ → Transverse b₂ b₃ → Transverse b₁ b₃ →
        ∀ (p : ↥(isect b₁ b₂)) (q : ↥(isect b₂ b₃)) (ξ : ↥(isect b₁ b₃) →₀ ℂ),
          (∀ r, ξ r = mTwoCoeff area b₁ b₂ b₃ p q r) →
          C.m [ψ b₁ b₂ (Finsupp.single p 1), ψ b₂ b₃ (Finsupp.single q 1)] = ψ b₁ b₃ ξ) := by
  sorry

end KontsevichHMS
