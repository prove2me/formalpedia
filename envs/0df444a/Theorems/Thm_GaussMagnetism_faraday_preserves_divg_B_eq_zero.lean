-- Prove2me | Theorems.Thm_GaussMagnetism_faraday_preserves_divg_B_eq_zero
-- name    : GaussMagnetism.faraday_preserves_divg_B_eq_zero
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-27T20:09:39.003532+00:00
-- url     : https://prove2.me/theorems/e767f8aa-1169-439a-a6e4-ae4ec516b213
-- title:
--   Faraday's law propagates $\nabla\cdot B=0$ from the initial time
-- statement:
--   Let $E,B:\mathbb R\times\mathbb R^3\to\mathbb R^3$ be time-dependent electric and magnetic fields that are smooth jointly in time $t$ and position $x$, and suppose they satisfy the Maxwell–Faraday law
--
--   $$\nabla\times E(t,\cdot)(x)=-\frac{\partial B}{\partial t}(t,x)\quad\text{for all }t\in\mathbb R,\ x\in\mathbb R^3.$$
--
--   If Gauss's law for magnetism holds at the initial time, $\nabla\cdot B(0,\cdot)(x)=0$ for all $x$, then it holds at every time: $\nabla\cdot B(t,\cdot)(x)=0$ for all $t\in\mathbb R$ and $x\in\mathbb R^3$.
--
--   This is the magnetic half of the redundancy of Maxwell's equations: a system satisfying Faraday's law automatically satisfies Gauss's law for magnetism, as long as the initial condition does.
--
--   **Formalization Note** Joint smoothness is `TongEM.SmoothTV`. The time derivative is Lean's `deriv` in $t$ at fixed $x$. Divergence and curl act on the spatial variable only. Times $t<0$ are included.
-- source:
--   Wikipedia, "Maxwell's equations" (uploaded PDF, 24 pp.), p. 16, section 'Overdetermination of Maxwell's equations': 'any system satisfying Faraday's law and Ampère's circuital law automatically also satisfies the two Gauss's laws, as long as the system's initial condition does' (magnetic part).

import Definitions.Def_GaussMagnetism_box_flux

open Larmor TongEM

namespace GaussMagnetism

theorem faraday_preserves_divg_B_eq_zero (E B : ℝ → Vec → Vec)
    (hE : SmoothTV E) (hB : SmoothTV B)
    (hfaraday : ∀ t x, curl (E t) x = -deriv (fun s => B s x) t)
    (hinit : ∀ x, divg (B 0) x = 0) :
    ∀ t x, divg (B t) x = 0 := by sorry

end GaussMagnetism
