-- Prove2me | Theorems.Thm_LanglandsTunnell_Converse_ArchR_eq_mul_of_unip_law_of_central_law_of_archWeightChar_of_torus_eq_of_sign_det
-- name    : LanglandsTunnell.Converse.ArchR.eq_mul_of_unip_law_of_central_law_of_archWeightChar_of_torus_eq_of_sign_det
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:00.858323+00:00
-- url     : https://prove2.me/theorems/573eaa07-8bb9-5429-9f03-d25b039abda4
-- title:
--   Torus rays determine a ψ-Whittaker function of weight k
-- statement:
--   Let $A,B\colon M_2(\mathbb R)\to\mathbb C$ be functions, $k\in\mathbb Z$, and $e,z\in\mathbb C$. Assume four pairs of transformation laws. First, for every $t\in\mathbb R$ and every $x\in M_2(\mathbb R)$ with $\det x\neq 0$, $A(\,!![1,t;0,1]\cdot x) = e^{2\pi i t}A(x)$, and the same for $B$. Second, for every real $t>0$ and every $x$ with $\det x\neq 0$, $A(t\cdot x) = t^{e}A(x)$, and the same for $B$ (scalars only, and only positive ones). Third, for every $r$ in the subgroup `rowIsometrySubgroup₀ ℝ` of $GL_2(\mathbb R)$ and every $x\in GL_2(\mathbb R)$, $A(xr) = \chi(r)A(x)$, where $\chi$ is the value of the archimedean weight character `archWeightCharℝ k` at $r$, coerced to $\mathbb C$; likewise for $B$. Finally, let $\varepsilon\in\mathbb R$ with $\varepsilon = 1$ or $\varepsilon = -1$, and suppose that on the corresponding torus ray the two functions are proportional with factor $z$: $A\big(\mathrm{diag}(\varepsilon\sqrt y,(\sqrt y)^{-1})\big) = z\,B\big(\mathrm{diag}(\varepsilon\sqrt y,(\sqrt y)^{-1})\big)$ for all real $y>0$. The conclusion is that $A(x) = z\,B(x)$ for every $x\in M_2(\mathbb R)$ with $\varepsilon\det x>0$.
--
--   This is the uniqueness statement underlying the archimedean theory of Whittaker functions on $GL_2(\mathbb R)$: via the Iwasawa decomposition, a function with prescribed $\psi$-law on upper unipotents, prescribed behaviour under positive scalars and prescribed weight-$k$ behaviour on the right is determined, on each of the two determinant-sign components, by its restriction to the corresponding torus ray. It is used in the real archimedean computations of the converse direction, for instance in the results on the vanishing of $W$ on matrices of negative determinant and on the values of $W$ on diagonal matrices in the principal and discrete series cases.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_Converse_ArchR_eq_mul_of_unip_law_of_central_law_of_archWeightChar_of_torus_eq_of_sign_det.lean

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

theorem LanglandsTunnell.Converse.ArchR.eq_mul_of_unip_law_of_central_law_of_archWeightChar_of_torus_eq_of_sign_det
    (A B : Matrix (Fin 2) (Fin 2) ℝ → ℂ) (k : ℤ) (e z : ℂ)
    (hAN : ∀ (t : ℝ) (x : Matrix (Fin 2) (Fin 2) ℝ), x.det ≠ 0 → A (ArchR.unip t * x) = ArchR.psi t * A x)
    (hBN : ∀ (t : ℝ) (x : Matrix (Fin 2) (Fin 2) ℝ), x.det ≠ 0 → B (ArchR.unip t * x) = ArchR.psi t * B x)
    (hAZ : ∀ (t : ℝ) (x : Matrix (Fin 2) (Fin 2) ℝ), 0 < t → x.det ≠ 0 → A (t • x) = ((t : ℂ) ^ e) * A x)
    (hBZ : ∀ (t : ℝ) (x : Matrix (Fin 2) (Fin 2) ℝ), 0 < t → x.det ≠ 0 → B (t • x) = ((t : ℂ) ^ e) * B x)
    (hAK : ∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
      A ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
        (archWeightCharℝ k r : ℂ) * A (x : Matrix (Fin 2) (Fin 2) ℝ))
    (hBK : ∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
      B ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
        (archWeightCharℝ k r : ℂ) * B (x : Matrix (Fin 2) (Fin 2) ℝ))
    (ε : ℝ) (hε : ε = 1 ∨ ε = -1)
    (htor : ∀ y : ℝ, 0 < y →
      A !![ε * Real.sqrt y, 0; 0, (Real.sqrt y)⁻¹] = z * B !![ε * Real.sqrt y, 0; 0, (Real.sqrt y)⁻¹])
    (x : Matrix (Fin 2) (Fin 2) ℝ) (hx : 0 < ε * x.det) :
    A x = z * B x := by sorry
