-- Prove2me | Theorems.Thm_NoetherIVP_lagrange_central_identity
-- name    : NoetherIVP.lagrange_central_identity
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-15T14:54:37.924467+00:00
-- url     : https://prove2.me/theorems/8ae8fc26-6d51-4874-a012-c07ed28fba34
-- title:
--   Noether (1918), eq. (3): $\sum_i \psi_i \delta u_i = \delta f + \operatorname{Div} A$
-- statement:
--   **Equation (3) of the paper** (in the $n$-dimensional form (5)): the identity produced by
--   partially integrating the first variation of $\int f\,dx$.
--
--   Let $f$ be a first-order Lagrangian, $u$ a field, and $\delta u$ an arbitrary variation field.
--   At a point $x$ at which each component $y \mapsto \delta u(y)_i$ and each momentum
--   $y \mapsto p_{l i}[u](y)$ is differentiable,
--   $$\sum_{i=1}^{m} \psi_i[u](x)\,\delta u(x)_i \;=\; \delta f(x) \;+\; \operatorname{Div}A(x),
--   \qquad A_l \;=\; -\sum_{i=1}^{m} p_{l i}[u]\,\delta u_i .$$
--   The Lagrange expressions $\psi_i$ are thus exactly what remains of the first variation once
--   the divergence of the boundary vector $A$ has been split off. This is the identity Noether
--   uses throughout §2, and the one she calls, for a single independent variable, Heun's
--   "central equation of Lagrange" (equation (4)).
-- source:
--   E. Noether, Invariante Variationsprobleme (1918), Tavel translation, arXiv:physics/0503066v3, §1, p. 2, equation (3) (n-dimensional form: equation (5)).

import Mathlib
import Definitions.Def_NoetherIVP_core

namespace NoetherIVP
theorem lagrange_central_identity {n m : ℕ}
    (f : (Fin n → ℝ) → (Fin m → ℝ) → (Fin n → Fin m → ℝ) → ℝ)
    (u du : (Fin n → ℝ) → Fin m → ℝ) (x : Fin n → ℝ)
    (hdu : ∀ i : Fin m, DifferentiableAt ℝ (fun y => du y i) x)
    (hmom : ∀ (l : Fin n) (i : Fin m), DifferentiableAt ℝ (mom f u l i) x) :
    ∑ i : Fin m, lagrangeExpr f u i x * du x i
      = varF f u du x + divg (bdryA f u du) x := by sorry
end NoetherIVP
