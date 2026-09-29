-- Prove2me | Theorems.Thm_ModularCurve_realizeOf_eq_div
-- name    : ModularCurve.realizeOf_eq_div
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.618386+00:00
-- url     : https://prove2.me/theorems/189c50d4-7af7-5360-ad95-f58a8c9162f0
-- title:
--   Independence of the realisation from the chosen presentation
-- statement:
--   Let $\Gamma \le \mathrm{SL}_2(\mathbb{Z})$ be a subgroup containing the translation matrix `ModularGroup.T`, let $k \in \mathbb{Z}$, and let $g, h$ be modular forms of weight $k$ on $\Gamma$. Let $x$ be a Laurent series over $\mathbb{C}$ and suppose that $x$ times the image in $\mathbb{C}((q))$ of the period-$1$ $q$-expansion of $h$ equals the image of the period-$1$ $q$-expansion of $g$. Let $\tau$ lie in the upper half plane and suppose $h(\tau) \neq 0$. Then [`ModularCurve.realizeOf`](def/ModularCurve_ComplexPlaceDictionaryOf.html#L15) $\Gamma\, x\, \tau$ equals $g(\tau)/h(\tau)$. Here [`ModularCurve.realizeOf`](def/ModularCurve_ComplexPlaceDictionaryOf.html#L15) $\Gamma\, x\, \tau$ is defined by cases: if there exists a triple consisting of a weight $j \in \mathbb{Z}$ and a pair $(G, H)$ of modular forms of weight $j$ on $\Gamma$ with $H(\tau) \neq 0$ and $x \cdot \widetilde{H} = \widetilde{G}$ in $\mathbb{C}((q))$ (tilde denoting the period-$1$ $q$-expansion pushed into Laurent series), it is $G(\tau)/H(\tau)$ for one such triple chosen by the axiom of choice, and otherwise it is $0$. Thus the assertion is that the chosen value agrees with the value computed from the given presentation $x \cdot \widetilde{h} = \widetilde{g}$.
--
--   This is the well-definedness statement for the realisation of a Laurent series as a meromorphic function on the upper half plane as a ratio of modular forms of equal weight on $\Gamma$: the value at $\tau$ does not depend on the presentation. It underlies the complex-place dictionary for modular curves and is invoked throughout that development, for instance in the treatment of Abel–Jacobi images, of the action of complex conjugation on points, and of stabiliser orders and ramification.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_realizeOf_eq_div.lean

import Mathlib
import Definitions.Def_ModularCurve_ComplexPlaceDictionaryOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.realizeOf_eq_div
    (Γ : Subgroup SL(2, ℤ)) (hT : ModularGroup.T ∈ Γ) {k : ℤ}
    (g h : ModularForm Γ k) (x : LaurentSeries ℂ)
    (hx : x * ((UpperHalfPlane.qExpansion 1 (h : UpperHalfPlane → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) =
      ((UpperHalfPlane.qExpansion 1 (g : UpperHalfPlane → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ))
    (τ : UpperHalfPlane) (hτ : (h : UpperHalfPlane → ℂ) τ ≠ 0) :
    ModularCurve.realizeOf Γ x τ = (g : UpperHalfPlane → ℂ) τ / (h : UpperHalfPlane → ℂ) τ := by sorry
