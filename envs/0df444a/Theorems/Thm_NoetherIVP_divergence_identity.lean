-- Prove2me | Theorems.Thm_NoetherIVP_divergence_identity
-- name    : NoetherIVP.divergence_identity
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-15T14:57:30.853541+00:00
-- url     : https://prove2.me/theorems/53851a6b-efa4-412f-bbe6-3a77f8546728
-- title:
--   Noether (1918), eq. (12): $\sum_i \psi_i \delta u_i = \operatorname{Div} B$ with $B = A - f\,\Delta x$
-- statement:
--   **Equation (12) of the paper.** Combining the central identity (3) with Lie's differential
--   equation (11) gives, for a single infinitesimal transformation, the divergence identity
--   $$\sum_{i=1}^{m} \psi_i[u]\,\delta u_i \;=\; \operatorname{Div} B, \qquad B \;=\; A - f[u]\,\Delta x .$$
--   Noether writes that this relation "for every invariant integral $I$ represents an identity in all
--   arguments that occur; it is the required form of Lie's differential equations for $I$".
--
--   Formally: at a point $x$ where the relevant functions are differentiable and where
--   $\delta f(x) + \operatorname{Div}(f[u]\,\Delta x)(x) = 0$, one has
--   $\sum_i \psi_i[u](x)\,\delta u(x)_i = \operatorname{Div}B(x)$.
-- source:
--   E. Noether, Invariante Variationsprobleme (1918), Tavel translation, arXiv:physics/0503066v3, §2, p. 5, equation (12).

import Mathlib
import Definitions.Def_NoetherIVP_core

namespace NoetherIVP
theorem divergence_identity {n m : ℕ}
    (f : (Fin n → ℝ) → (Fin m → ℝ) → (Fin n → Fin m → ℝ) → ℝ)
    (u du : (Fin n → ℝ) → Fin m → ℝ) (dx : (Fin n → ℝ) → Fin n → ℝ) (x : Fin n → ℝ)
    (hdu : ∀ i : Fin m, DifferentiableAt ℝ (fun y => du y i) x)
    (hmom : ∀ (l : Fin n) (i : Fin m), DifferentiableAt ℝ (mom f u l i) x)
    (hfdx : ∀ l : Fin n, DifferentiableAt ℝ (fun y => lagr f u y * dx y l) x)
    (hinv : varF f u du x + divg (fun z l => lagr f u z * dx z l) x = 0) :
    ∑ i : Fin m, lagrangeExpr f u i x * du x i = divg (curB f u du dx) x := by sorry
end NoetherIVP
