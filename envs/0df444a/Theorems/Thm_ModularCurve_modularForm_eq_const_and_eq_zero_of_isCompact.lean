-- Prove2me | Theorems.Thm_ModularCurve_modularForm_eq_const_and_eq_zero_of_isCompact
-- name    : ModularCurve.modularForm_eq_const_and_eq_zero_of_isCompact
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.624895+00:00
-- url     : https://prove2.me/theorems/6fc34a2e-d5ce-531b-a8b9-d7b4c130a819
-- title:
--   Non-positive weight forms for cocompact discrete Γ
-- statement:
--   Let $\Gamma$ be a subgroup of $\mathrm{GL}_2(\mathbb{R})$ all of whose elements have determinant $1$, carrying the discrete topology as a subspace, and suppose $\Gamma$ acts cocompactly on the upper half-plane $\mathbb{H}$ in the following explicit sense: there is a set $K \subseteq \mathbb{H}$ that is compact and such that for every $\tau \in \mathbb{H}$ some $\gamma \in \Gamma$ satisfies $\gamma \cdot \tau \in K$, i.e. $K$ meets every $\Gamma$-orbit. The conclusion is the conjunction of two assertions about Mathlib's spaces of modular forms for $\Gamma$. First, for every modular form $f$ of weight $0$ for $\Gamma$ there is a constant $c \in \mathbb{C}$ with the underlying function $\mathbb{H} \to \mathbb{C}$ of $f$ equal to the constant function with value $c$. Second, for every integer $k < 0$ and every modular form $f$ of weight $k$ for $\Gamma$, the underlying function $\mathbb{H} \to \mathbb{C}$ of $f$ is identically zero. Thus $M_0(\Gamma) = \mathbb{C}$ and $M_k(\Gamma) = 0$ for $k < 0$, with no hypothesis imposed at cusps beyond what the definition of a modular form already contains.
--
--   This is the standard vanishing statement for automorphic forms of non-positive weight on a cocompact discrete group of determinant-one real matrices, the function-theoretic input showing that the field of weight-zero automorphic functions contains no extra holomorphic elements. It is used by [`ModularCurve.isCurveOver_automorphicField_of_isCompact`](thm.html#ModularCurve.isCurveOver_automorphicField_of_isCompact), which identifies the field of automorphic functions attached to such a $\Gamma$ as the function field of a curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_modularForm_eq_const_and_eq_zero_of_isCompact.lean

import Mathlib.NumberTheory.ModularForms.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups Topology Manifold
open UpperHalfPlane

theorem ModularCurve.modularForm_eq_const_and_eq_zero_of_isCompact
    (Γ : Subgroup (GL (Fin 2) ℝ)) [Γ.HasDetOne]
    [hdisc : DiscreteTopology ↥Γ]
    (hcpt : ∃ K : Set ℍ, IsCompact K ∧ ∀ τ : ℍ, ∃ γ ∈ Γ, γ • τ ∈ K) :
    (∀ f : ModularForm Γ 0, ∃ c : ℂ, (f : ℍ → ℂ) = fun _ => c) ∧
    (∀ k : ℤ, k < 0 → ∀ f : ModularForm Γ k, (f : ℍ → ℂ) = 0) := by sorry
