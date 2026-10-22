-- Prove2me | Theorems.Thm_NCLpModules_Principal_proposition_2_2_triangle
-- name    : NCLpModules.Principal.proposition_2_2_triangle
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:45:58.165391+00:00
-- url     : https://prove2.me/theorems/a8a5a59e-e18c-401a-bd06-a41f76a15e67
-- title:
--   Proposition 2.2, p. 8 — ‖ξ‖ = ‖⟨ξ,ξ⟩^{1/2}‖_p is a norm for p ≥ 2 and a p/2-norm for p ≤ 2
-- statement:
--   Let $\mathcal M\subseteq M_n(\mathbb C)$ be a unital $*$-subalgebra, $0<p<\infty$, and $\mathfrak X$ a right $\mathcal M$-module with an $L^{p/2}$-valued inner product. Put $\|\xi\|=\|\langle\xi,\xi\rangle^{1/2}\|_p$. Then $\|\xi\|\ge0$, $\|\xi\|=0$ iff $\xi=0$, $\|c\xi\|=|c|\,\|\xi\|$ for $c\in\mathbb C$, and
--
--   1. if $p\ge2$, $\|\cdot\|$ is a norm: $\ \|\xi+\eta\|\le\|\xi\|+\|\eta\|$;
--   2. if $p\le2$, $\|\cdot\|$ is a $p/2$-norm:
--   $$\|\xi+\eta\|^{p/2}\le\|\xi\|^{p/2}+\|\eta\|^{p/2}.$$
--
--   This makes $\|\cdot\|$ the (quasi)norm in which Definition 2.3 asks an $L^p$ module to be complete.
--
--   **Formalization Note** Finite-dimensional scope. The norm is `gauge p ip ξ` $=\big(\mathrm{Tr}\,\langle\xi,\xi\rangle^{p/2}\big)^{1/p}$; the $p/2$-norm inequality is the one the proof derives on p. 9 ("Therefore $\|\xi+\eta\|^{p/2}\le\|\xi\|^{p/2}+\|\eta\|^{p/2}$"). Nonnegativity, definiteness and homogeneity are stated once for all $p$ since they hold in both cases.
-- source:
--   Junge & Sherman, Noncommutative Lp modules, arXiv:math/0301044v2, p. 8, Proposition 2.2 (last sentence), proof p. 9, (2.3)

import Mathlib
import Definitions.Def_NCLpModules_Principal_Model

namespace NCLpModules.Principal

open scoped Matrix ComplexOrder

theorem proposition_2_2_triangle {n : ℕ} (M : StarSubalgebra ℂ (Matrix (Fin n) (Fin n) ℂ))
    {p : ℝ} (hp : 0 < p)
    {𝔛 : Type*} [AddCommGroup 𝔛] [Module ℂ 𝔛]
    (act : 𝔛 → Matrix (Fin n) (Fin n) ℂ → 𝔛) (hact : IsRightModuleAction M 𝔛 act)
    (ip : LpInnerProduct M 𝔛 act) :
    (∀ ξ : 𝔛, 0 ≤ gauge p ip ξ) ∧
      (∀ ξ : 𝔛, gauge p ip ξ = 0 ↔ ξ = 0) ∧
      (∀ (c : ℂ) (ξ : 𝔛), gauge p ip (c • ξ) = ‖c‖ * gauge p ip ξ) ∧
      (2 ≤ p → ∀ ξ η : 𝔛, gauge p ip (ξ + η) ≤ gauge p ip ξ + gauge p ip η) ∧
      (p ≤ 2 → ∀ ξ η : 𝔛,
        gauge p ip (ξ + η) ^ (p / 2) ≤ gauge p ip ξ ^ (p / 2) + gauge p ip η ^ (p / 2)) := by sorry

end NCLpModules.Principal
