-- Prove2me | Theorems.Thm_GeomDL_GroupConv_eq_14_equivariant
-- name    : GeomDL.GroupConv.eq_14_equivariant
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T13:41:25.526236+00:00
-- url     : https://prove2.me/theorems/60594e0b-86e2-47fa-98d7-9e5805b345e1
-- title:
--   §4.3, p. 41 — group convolution against an invariant measure is equivariant
-- statement:
--   Let $G$ act transitively and measurably on a domain $\Omega$, and let $\mu$ be invariant under the action. For scalar signals $x,\theta:\Omega\to\mathbb R$, a group element $h$, and an output index $g\in G$, group convolution satisfies
--
--   $$
--   ((\rho(h)x)\star\theta)(g)
--   =(x\star\theta)(h^{-1}g)
--   =(\rho_G(h)(x\star\theta))(g).
--   $$
--
--   Thus the convolution maps signals on $\Omega$ to signals on $G$ while respecting the two corresponding group actions.
--
--   **Formalization Note** In Lean the stated equality is between the first and last expressions; the middle expression is the definition of the regular action $\rho_G$. Transitivity records the section's homogeneous-domain assumption on p. 43. The book's invariant measure is explicit, as is measurability of the action. No integrability hypothesis is added; measure-preserving reindexing preserves the integral's value, including Lean's zero value for a nonintegrable integrand.
-- source:
--   Bronstein et al., Geometric Deep Learning (arXiv:2104.13478v2), §4.3, equation (14) and displayed equivariance identity, p. 41

import Mathlib
import Definitions.Def_GeomDL_GroupConv_Model

namespace GeomDL.GroupConv

universe u v

/-- §4.3, equation (14) and the following displayed identity, p. 41. -/
theorem eq_14_equivariant {G : Type u} {Ω : Type v} [Group G] [MulAction G Ω]
    [MeasurableSpace G] [MeasurableSpace Ω] [MeasurableSMul G Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.SMulInvariantMeasure G Ω μ]
    (htrans : ∀ a b : Ω, ∃ k : G, k • a = b)
    (h : G) (x θ : Ω → ℝ) (g : G) :
    groupConvolution μ (signalAction h x) θ g =
      regularAction h (groupConvolution μ x θ) g := by sorry

end GeomDL.GroupConv
