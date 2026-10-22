-- Prove2me | Theorems.Thm_GeomDL_GroupConv_representation_property
-- name    : GeomDL.GroupConv.representation_property
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T13:41:21.190766+00:00
-- url     : https://prove2.me/theorems/488958c3-24f9-4786-92ee-d4f56a332b4f
-- title:
--   §4.3, p. 41 — the induced signal action obeys the group representation law
-- statement:
--   Let $G$ act on a domain $\Omega$, and let $\rho(g)$ act on real-valued signals by $(\rho(g)\theta)(u)=\theta(g^{-1}\cdot u)$. For $h,g\in G$ and any filter $\theta$,
--
--   $$
--   \rho(h^{-1})(\rho(g)\theta)=\rho(h^{-1}g)\theta.
--   $$
--
--   The book uses this law to identify the transformed filter that appears in group convolution.
-- source:
--   Bronstein et al., Geometric Deep Learning (arXiv:2104.13478v2), §4.3, p. 41, paragraph following equation (14)

import Mathlib
import Definitions.Def_GeomDL_GroupConv_Model

namespace GeomDL.GroupConv

universe u v

/-- §4.3, p. 41: the signal action satisfies the representation law used in the displayed calculation. -/
theorem representation_property {G : Type u} {Ω : Type v} [Group G] [MulAction G Ω]
    (h g : G) (θ : Ω → ℝ) :
    signalAction h⁻¹ (signalAction g θ) = signalAction (h⁻¹ * g) θ := by sorry

end GeomDL.GroupConv
