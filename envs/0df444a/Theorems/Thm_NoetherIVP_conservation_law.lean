-- Prove2me | Theorems.Thm_NoetherIVP_conservation_law
-- name    : NoetherIVP.conservation_law
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-15T14:57:52.757987+00:00
-- url     : https://prove2.me/theorems/3dd4762a-6ed8-4f6a-bcad-81917f549982
-- title:
--   Noether (1918), §3: $\operatorname{Div}B = 0$ on solutions of the Lagrange equations
-- statement:
--   **§3 of the paper, "laws of conservation".** Passing from the identity (12) to the variational
--   problem itself — that is, imposing the Euler–Lagrange equations $\psi_i = 0$ — turns the
--   divergence identity into a conservation law:
--   $$\operatorname{Div} B \;=\; 0 .$$
--   Noether notes that in the one-dimensional case this yields $B = \text{const.}$, i.e. a first
--   integral, and that in the multidimensional case these are "the divergence equations often
--   referred to of late as 'laws of conservation'".
--
--   Formally: under the differentiability hypotheses of (12), if the invariance identity (11) holds at
--   $x$ and every Lagrange expression $\psi_i[u]$ vanishes identically, then $\operatorname{Div}B(x) = 0$.
-- source:
--   E. Noether, Invariante Variationsprobleme (1918), Tavel translation, arXiv:physics/0503066v3, §3, p. 7 (passage to the variation problem, psi = 0; 'laws of conservation'), following equation (13).

import Mathlib
import Definitions.Def_NoetherIVP_core

namespace NoetherIVP
theorem conservation_law {n m : ℕ}
    (f : (Fin n → ℝ) → (Fin m → ℝ) → (Fin n → Fin m → ℝ) → ℝ)
    (u du : (Fin n → ℝ) → Fin m → ℝ) (dx : (Fin n → ℝ) → Fin n → ℝ) (x : Fin n → ℝ)
    (hdu : ∀ i : Fin m, DifferentiableAt ℝ (fun y => du y i) x)
    (hmom : ∀ (l : Fin n) (i : Fin m), DifferentiableAt ℝ (mom f u l i) x)
    (hfdx : ∀ l : Fin n, DifferentiableAt ℝ (fun y => lagr f u y * dx y l) x)
    (hinv : varF f u du x + divg (fun z l => lagr f u z * dx z l) x = 0)
    (hEL : ∀ (i : Fin m) (y : Fin n → ℝ), lagrangeExpr f u i y = 0) :
    divg (curB f u du dx) x = 0 := by sorry
end NoetherIVP
