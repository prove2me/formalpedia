-- Prove2me | Theorems.Thm_LanglandsTunnell_Converse_ArchDatumR_negSheet_ode_and_growth_and_mellin_eq_of_archWeightChar_of_isCasimirEigen
-- name    : LanglandsTunnell.Converse.ArchDatumR.negSheet_ode_and_growth_and_mellin_eq_of_archWeightChar_of_isCasimirEigen
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:00.858323+00:00
-- url     : https://prove2.me/theorems/3195000e-e55d-504a-a584-153e3f54d4b1
-- title:
--   Whittaker ODE, growth and Mellin shape on the negative sheet
-- statement:
--   Let $P$ be a real archimedean parameter, $D$ an `ArchDatumR` for $P$ (so its function $W$ on real $2\times 2$ matrices is smooth on the invertible locus, transforms by $\psi$ under left unipotent translation, obeys the central law for $P$, and carries the zeta/functional-equation and decay data of the structure), and let $k_0$ be an integer. Assume: (i) $W$ has right weight $k_0$, i.e. $W(x\,r) = \mathrm{archWeightChar}_{\mathbb R}(k_0)(r)\, W(x)$ for every $r$ in `rowIsometrySubgroup₀ ℝ` and every $x \in \mathrm{GL}_2(\mathbb R)$; (ii) `ArchCasimir.IsCasimirEigen D`, that is $-\bigl(\tfrac14 H^2 W - \tfrac12 H W + E F_- W\bigr)(x) = \lambda(P)\,W(x)$ for all $x$ with $\det x \neq 0$, where $\lambda(P)$ is the Laplace eigenvalue of $P$ and $H,E,F_-$ denote the flow derivatives in those directions; (iii) $\lambda(P) = \tfrac14 - \nu^2$ for a given $\nu \in \mathbb C$; (iv) for a given $c_0 \in \mathbb C$, both sign twists of the archimedean factor are $\Gamma_{\mathbb C}$-shaped: $(P.\mathrm{twist}\,0\,a).\mathrm{archFactor}(s) = \Gamma_{\mathbb C}(s + c_0)$ for all $a \in \mathbb Z/2$ and all $s$. Set $f(y) = W\!\begin{pmatrix}-\sqrt y & 0\\ 0 & (\sqrt y)^{-1}\end{pmatrix}$, the restriction of $W$ to the determinant $-1$ torus ray. Then: $f$ and $f'$ are differentiable on $(0,\infty)$ and $y^2 f''(y) + \bigl(\tfrac14 - \nu^2 + 2\pi(-k_0)y - 4\pi^2 y^2\bigr) f(y) = 0$ for all $y>0$; there exist $C, N \in \mathbb R$ with $\|f(y)\| \le C y^N$ for all $y \ge 1$; and there exist $\sigma_0 \in \mathbb R$ and an entire $\Psi : \mathbb C \to \mathbb C$ such that for every $s$ with $\operatorname{Re} s > \sigma_0$ the Mellin integral of $f$ at $s$ converges and $\mathrm{mellin}\,f\,(s) = \Gamma_{\mathbb C}\bigl(s + c_0 - \tfrac{e-1}{2}\bigr)\Psi(s)$, where $e$ is the central exponent of $P$.
--
--   This is the analytic package for the negative-determinant sheet of the torus of a Whittaker datum at a real place: the weight $-k_0$ Whittaker differential equation, moderate growth at infinity, and the $\Gamma_{\mathbb C}$-shape of the Mellin transform obtained from the local zeta integrals against the two sign characters. It is used in the proofs that $W$ vanishes on matrices of negative determinant, for discrete parameters and for principal parameters with weight character trivial.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_Converse_ArchDatumR_negSheet_ode_and_growth_and_mellin_eq_of_archWeightChar_of_isCasimirEigen.lean

import Mathlib
import Definitions.Def_LanglandsTunnell_JLConverse
import Definitions.Def_LanglandsTunnell_ArchCasimirCompanion
import Definitions.Def_AutomorphicForm_ArchWeightChar
import Definitions.Def_AutomorphicForm_ArchDerivCasimir

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Real Complex
open NumberField AutomorphicForm
open LanglandsTunnell LanglandsTunnell.RealArchParam LanglandsTunnell.Converse

theorem LanglandsTunnell.Converse.ArchDatumR.negSheet_ode_and_growth_and_mellin_eq_of_archWeightChar_of_isCasimirEigen
    (P : RealArchParam) (D : ArchDatumR P) (k₀ : ℤ)
    (hDW : ∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
      D.W ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
        (archWeightCharℝ k₀ r : ℂ) * D.W (x : Matrix (Fin 2) (Fin 2) ℝ))
    (hDE : ArchCasimir.IsCasimirEigen D)
    (ν : ℂ) (hν : P.laplaceEigenvalue = 1 / 4 - ν ^ 2)
    (c₀ : ℂ) (hA : ∀ (a : ZMod 2) (s : ℂ), (P.twist 0 a).archFactor s = Complex.Gammaℂ (s + c₀)) :
    let f : ℝ → ℂ := fun y => D.W !![-Real.sqrt y, 0; 0, (Real.sqrt y)⁻¹]
    (DifferentiableOn ℝ f (Set.Ioi 0) ∧ DifferentiableOn ℝ (deriv f) (Set.Ioi 0) ∧
      ∀ y : ℝ, 0 < y →
        (y : ℂ) ^ 2 * deriv (deriv f) y
            + (1 / 4 - ν ^ 2 + 2 * (π : ℂ) * ((-(k₀ : ℝ) : ℝ) : ℂ) * (y : ℂ) - 4 * (π : ℂ) ^ 2 * (y : ℂ) ^ 2) * f y = 0) ∧
    (∃ C N : ℝ, ∀ y : ℝ, 1 ≤ y → ‖f y‖ ≤ C * y ^ N) ∧
    (∃ (σ₀ : ℝ) (Ψ : ℂ → ℂ), Differentiable ℂ Ψ ∧
      ∀ s : ℂ, σ₀ < s.re →
        MellinConvergent (fun y : ℝ => f y) s ∧
          mellin (fun y : ℝ => f y) s = Complex.Gammaℂ (s + (c₀ - (P.centralExponent - 1) / 2)) * Ψ s) := by sorry
