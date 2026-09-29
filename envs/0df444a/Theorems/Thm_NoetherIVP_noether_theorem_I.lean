-- Prove2me | Theorems.Thm_NoetherIVP_noether_theorem_I
-- name    : NoetherIVP.noether_theorem_I
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-15T14:59:08.52777+00:00
-- url     : https://prove2.me/theorems/85e2fcbd-1f20-4e3e-a2a5-fb63a04121ac
-- title:
--   Noether's Theorem I (1918), eq. (13): $\rho$ divergence relations from a $G_\rho$
-- statement:
--   **Theorem I of the paper**, in the form of equation (13), for a first-order Lagrangian.
--
--   Let $f$ be a Lagrangian, $u$ a field, and let $\rho$ infinitesimal transformations be given by
--   generators $\Delta x^{(r)}$ on the independent variables and $\Delta u^{(r)}$ on the dependent ones,
--   $r = 1,\dots,\rho$. Let $\delta u^{(r)}$ be the associated variations at fixed $x$ of equation (9),
--   $$\delta u^{(r)}_i \;=\; \Delta u^{(r)}_i \;-\; \sum_{l}\frac{\partial u_i}{\partial x_l}\,\Delta x^{(r)}_l .$$
--   If the integral $I = \int f\,dx$ is invariant under each of them — that is, if Lie's differential
--   equation (11) $\delta f^{(r)} + \operatorname{Div}\bigl(f[u]\,\Delta x^{(r)}\bigr) = 0$ holds
--   everywhere — then $\rho$ combinations of the Lagrange expressions become divergences:
--   $$\sum_{i=1}^{m} \psi_i[u]\,\delta u^{(r)}_i \;=\; \operatorname{Div} B^{(r)},
--   \qquad B^{(r)}_l \;=\; -\sum_{i} p_{l i}[u]\,\delta u^{(r)}_i \;-\; f[u]\,\Delta x^{(r)}_l ,$$
--   for every $r$ and at every point. These are the "laws of conservation" of the paper once the
--   Euler–Lagrange equations are imposed.
--
--   The linear independence of the $\rho$ relations, which Noether deduces from the essentiality of the
--   $\rho$ parameters, is not part of this statement.
-- source:
--   E. Noether, Invariante Variationsprobleme (1918), Tavel translation, arXiv:physics/0503066v3, §1, p. 3 (Theorem I) and §2, p. 5, equation (13).

import Mathlib
import Definitions.Def_NoetherIVP_core

namespace NoetherIVP
theorem noether_theorem_I {n m rho : ℕ}
    (f : (Fin n → ℝ) → (Fin m → ℝ) → (Fin n → Fin m → ℝ) → ℝ)
    (u : (Fin n → ℝ) → Fin m → ℝ) (Du : Fin rho → (Fin n → ℝ) → Fin m → ℝ)
    (Dx : Fin rho → (Fin n → ℝ) → Fin n → ℝ)
    (hdu : ∀ (r : Fin rho) (i : Fin m) (x : Fin n → ℝ),
      DifferentiableAt ℝ (fun y => deltaU u (Du r) (Dx r) y i) x)
    (hmom : ∀ (l : Fin n) (i : Fin m) (x : Fin n → ℝ),
      DifferentiableAt ℝ (mom f u l i) x)
    (hfdx : ∀ (r : Fin rho) (l : Fin n) (x : Fin n → ℝ),
      DifferentiableAt ℝ (fun y => lagr f u y * Dx r y l) x)
    (hinv : ∀ (r : Fin rho) (x : Fin n → ℝ),
      varF f u (deltaU u (Du r) (Dx r)) x
        + divg (fun z l => lagr f u z * Dx r z l) x = 0) :
    ∀ (r : Fin rho) (x : Fin n → ℝ),
      (∑ i : Fin m, lagrangeExpr f u i x * deltaU u (Du r) (Dx r) x i)
        = divg (curB f u (deltaU u (Du r) (Dx r)) (Dx r)) x := by sorry
end NoetherIVP
