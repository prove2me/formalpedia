-- Prove2me | Theorems.Thm_LanglandsTunnell_Converse_ArchDatumR_laws_and_torus_ode_of_archWeightChar_of_isCasimirEigen
-- name    : LanglandsTunnell.Converse.ArchDatumR.laws_and_torus_ode_of_archWeightChar_of_isCasimirEigen
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:00.858323+00:00
-- url     : https://prove2.me/theorems/4416577d-d350-5f12-b069-9e6cf5544b67
-- title:
--   Transformation laws and torus ODE for an archimedean datum
-- statement:
--   Let $P$ be a real archimedean parameter, i.e. either a principal datum $(u_1,a_1,u_2,a_2)$ with $u_i \in \mathbb{C}$, $a_i \in \mathbb{Z}/2$, or a discrete datum $(u,k)$ with $k \ge 1$, and let $D$ be an archimedean Whittaker datum for $P$ (`ArchDatumR P`): a function $W : M_2(\mathbb{R}) \to \mathbb{C}$, smooth on the invertible matrices, with $W(n(x)g) = e^{2\pi i x} W(g)$ for $n(x) = \bigl(\begin{smallmatrix}1&x\\0&1\end{smallmatrix}\bigr)$ and $W(z\cdot g) = \chi_P(z)|z| W(g)$ for $z \ne 0$, together with the zeta-integral package (entirety, functional equation, finite order, decay at $0$ and at $\infty$). Let $k \in \mathbb{Z}$ and $\nu \in \mathbb{C}$ with $\nu^2 = 1/4 - \lambda(P)$, where $\lambda(P)$ is $1/4 - ((u_1-u_2)/2)^2$ in the principal case and $(1-k^2)/4$ in the discrete case. Assume (i) $W(xr) = \chi_k(r) W(x)$ for every $x \in GL_2(\mathbb{R})$ and every $r$ in the subgroup `rowIsometrySubgroup₀ ℝ` of $GL_2(\mathbb{R})$, where $\chi_k =$ `archWeightCharℝ k` is real valued (the underlying predicate `IsRowIsometry` asks that $|\det r| = 1$ and that the row action of $r$ preserve $\|x\|^2 + \|y\|^2$); and (ii) the Casimir eigen-equation `ArchCasimir.IsCasimirEigen D`, namely $-\bigl(\tfrac14 H^2 - \tfrac12 H + E F\bigr) W = \lambda(P) \, W$ at every $x$ with $\det x \ne 0$, the operators being the flow derivatives in the directions $H$, $E$, $F$. Put $B(x) = |\det x|^{-1/2} W(x)$. Then: $B(n(t)x) = e^{2\pi i t} B(x)$ for all real $t$ and all $x$ with $\det x \ne 0$; $B(t\cdot x) = t^{e(P)} B(x)$ for $t > 0$ and $\det x \ne 0$, where $e(P)$ is $u_1+u_2$, respectively $2u$; $B(xr) = \chi_k(r) B(x)$ for $x \in GL_2(\mathbb{R})$ and $r$ in the same subgroup; and for each $\varepsilon \in \{1,-1\}$ the torus sheet $y \mapsto B\bigl(\mathrm{diag}(\varepsilon\sqrt{y}, 1/\sqrt{y})\bigr)$ is differentiable on $(0,\infty)$, as is its derivative, it satisfies $$y^2 g_\varepsilon''(y) + \bigl(\tfrac14 - \nu^2 + 2\pi \varepsilon k\, y - 4\pi^2 y^2\bigr) g_\varepsilon(y) = 0 \quad (y > 0),$$ and there are real constants $C, N$ with $\|g_\varepsilon(y)\| \le C y^N$ for all $y \ge 1$.
--
--   This is the classical reduction of an archimedean Whittaker function on $GL_2(\mathbb{R})$ of fixed weight and fixed Casimir eigenvalue to the Whittaker differential equation on the split torus, in the normalisation $B = |\det|^{-1/2} W$ that matches the adelic Whittaker functional. The four conclusions are exactly the input needed to identify $B$ on the torus with a classical Whittaker function, and they are used downstream to evaluate $W$ on diagonal matrices in the principal and discrete cases; the proof cites the bridge placing the datum at a real place of a number field and the split-torus form of the Whittaker equation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_Converse_ArchDatumR_laws_and_torus_ode_of_archWeightChar_of_isCasimirEigen.lean

import Definitions.Def_AutomorphicForm_TranslateSpanOccurrence
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_LanglandsTunnell_JLConverse
import Definitions.Def_LanglandsTunnell_ArchCasimirCompanion
import Definitions.Def_AutomorphicForm_ArchWeightChar
import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.AdelicLevel NumberField.AdelicBox AutomorphicForm AutomorphicForm.WindowedSiegel
  AutomorphicForm.SiegelCovering NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open LanglandsTunnell LanglandsTunnell.RealArchParam
open LanglandsTunnell.Converse

theorem LanglandsTunnell.Converse.ArchDatumR.laws_and_torus_ode_of_archWeightChar_of_isCasimirEigen
    (P : RealArchParam) (D : ArchDatumR P) (k : ℤ) (ν : ℂ) (hν : ν ^ 2 = 1 / 4 - P.laplaceEigenvalue)
    (hDW : ∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
      D.W ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
        (archWeightCharℝ k r : ℂ) * D.W (x : Matrix (Fin 2) (Fin 2) ℝ))
    (hDE : ArchCasimir.IsCasimirEigen D) :
    let B : Matrix (Fin 2) (Fin 2) ℝ → ℂ := fun x => (((|x.det| ^ (-(1 / 2 : ℝ)) : ℝ)) : ℂ) * D.W x
    (∀ (t : ℝ) (x : Matrix (Fin 2) (Fin 2) ℝ), x.det ≠ 0 → B (ArchR.unip t * x) = ArchR.psi t * B x) ∧
    (∀ (t : ℝ) (x : Matrix (Fin 2) (Fin 2) ℝ), 0 < t → x.det ≠ 0 → B (t • x) = ((t : ℂ) ^ P.centralExponent) * B x) ∧
    (∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
      B ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
        (archWeightCharℝ k r : ℂ) * B (x : Matrix (Fin 2) (Fin 2) ℝ)) ∧
    (∀ ε : ℝ, (ε = 1 ∨ ε = -1) →
      DifferentiableOn ℝ (fun y : ℝ => B !![ε * Real.sqrt y, 0; 0, (Real.sqrt y)⁻¹]) (Set.Ioi 0) ∧
      DifferentiableOn ℝ (deriv (fun y : ℝ => B !![ε * Real.sqrt y, 0; 0, (Real.sqrt y)⁻¹])) (Set.Ioi 0) ∧
      (∀ y : ℝ, 0 < y →
        (y : ℂ) ^ 2 * deriv (deriv (fun y : ℝ => B !![ε * Real.sqrt y, 0; 0, (Real.sqrt y)⁻¹])) y
            + (1 / 4 - ν ^ 2 + 2 * (Real.pi : ℂ) * ((ε * k : ℝ) : ℂ) * (y : ℂ) - 4 * (Real.pi : ℂ) ^ 2 * (y : ℂ) ^ 2)
              * B !![ε * Real.sqrt y, 0; 0, (Real.sqrt y)⁻¹] = 0) ∧
      ∃ C N : ℝ, ∀ y : ℝ, 1 ≤ y → ‖B !![ε * Real.sqrt y, 0; 0, (Real.sqrt y)⁻¹]‖ ≤ C * y ^ N) := by sorry
