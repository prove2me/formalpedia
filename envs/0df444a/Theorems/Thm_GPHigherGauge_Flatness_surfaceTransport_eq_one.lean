-- Prove2me | Theorems.Thm_GPHigherGauge_Flatness_surfaceTransport_eq_one
-- name    : GPHigherGauge.Flatness.surfaceTransport_eq_one
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:55:43.637401+00:00
-- url     : https://prove2.me/theorems/a7b2320e-1198-427b-abeb-48eb88d774f2
-- title:
--   Eq. (2.37) — the surface-transported holonomy $\mathcal F=g_2^{-1}t(h)g_1$ is the unit
-- statement:
--   Let $G$ be a group and $t:H\to G$ a map. Let $g_1,g_2\in G$ be the labels of the source and target curves of a surface and $h\in H$ its label, satisfying the surface condition $t(h)=g_2\,g_1^{-1}$. Then
--   $$\mathcal F=g_2^{-1}\,t(h)\,g_1=1 .$$
--
--   In 2-gauge theory the usual holonomy $g_2^{-1}g_1$ is replaced by this expression, which takes the surface transport into account; that it is always the unit is the identity behind level-1 flatness $\tau(B)=-F$.
--
--   Differences from the source:
--   - generalization: t the homomorphism of a crossed module of groups → any map t : H → G; reason: the identity uses only the surface condition (2.10); the crossed-module case is an instance.
--   - encoding: the labels g₁, g₂ of the source and target curves of a surface and its label h → arbitrary g₁ g₂ : G and h : H with t h = g₂ * g₁⁻¹; reason: the identity concerns only the labels, and the labels of a surface are such elements.
-- source:
--   Girelli, Pfeiffer, Higher gauge theory — differential versus integral formulation, arXiv:hep-th/0309173v2, §2.6, Eq. (2.37), p. 13

import Mathlib

namespace GPHigherGauge.Flatness

/-- The surface-transported holonomy is the unit.

Girelli, Pfeiffer, *Higher gauge theory — differential versus integral formulation*,
arXiv:hep-th/0309173v2, §2.6, Eq. (2.37), p. 13:
"Rather than the usual holonomy g_2^{-1} g_1, we should therefore consider the expression,
𝓕 = g_2^{-1} t(h) g_1, (2.37) which takes the surface transport into account. Due to condition
(2.10), however, this expression always gives the group unit of G, 𝓕 = 1."

For a surface with source label `g₁`, target label `g₂` and surface label `h` satisfying the
surface condition (2.10) `t(h) = g₂ · g₁⁻¹`, the expression `g₂⁻¹ t(h) g₁` equals `1`. This is
thin group algebra; it is the step "𝓕 = 1" that (3.25) invokes.

**Formalization Note** `t : H → G` is any map: neither the homomorphism property nor the action of
the crossed module is needed. -/
theorem surfaceTransport_eq_one {G : Type*} [Group G] {H : Type*} (t : H → G) (g₁ g₂ : G) (h : H)
    (hsurf : t h = g₂ * g₁⁻¹) : g₂⁻¹ * t h * g₁ = 1 := by sorry

end GPHigherGauge.Flatness
