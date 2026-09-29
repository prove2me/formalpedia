-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_isSchwartzBruhat_matFourier22
-- name    : LanglandsTunnell.CubicInduction.isSchwartzBruhat_matFourier22
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/3eecdb60-120d-542d-8258-2fde7a83da1b
-- title:
--   Schwartz–Bruhat functions on M₂ are stable under the matrix Fourier transform
-- statement:
--   Let $v$ be a point of the height-one spectrum of the ring of integers of $\mathbb{Q}$, write $F = \mathbb{Q}_v$ for the $v$-adic completion, and let $\eta$ be a $\mathbb{C}$-valued additive character of $F$. Let $n$ be an integer and assume that $\eta$ has exact level $n$ in the sense of the two hypotheses: $\eta(x) = 1$ for every $x \in F$ with $\mathrm{v}(x) \le \mathrm{exp}(n)$, and there exists $x \in F$ with $\mathrm{v}(x) \le \mathrm{exp}(n+1)$ and $\eta(x) \neq 1$. Let $\varphi : M_2(F) \to \mathbb{C}$ be Schwartz–Bruhat, i.e. locally constant and of compact support. The conclusion is that `matFourier22 v η φ` is again locally constant with compact support, where `matFourier22` is the composite of the two single-column transforms `colFourier22 v η 1` and then `colFourier22 v η 0`, and `colFourier22 v η j ψ` evaluated at $X \in M_2(F)$ is the integral over $u = (u_1,u_2) \in F \times F$, against the product of the self-dual Haar measure at $v$ with itself, of $\psi$ applied to $X$ with its $j$-th column replaced by $u$, times $\eta(u_1 X_{0j} + u_2 X_{1j})$.
--
--   This is the stability of the space of Schwartz–Bruhat functions on $2 \times 2$ matrices over a local field under the partial (column-by-column, hence full) Fourier transform attached to a character of exact level, as used in Tate-style local theory. It supplies the admissibility of the dual datum $\widehat\varphi$ in the Godement–Jacquet and Rankin–Selberg local integrals, and is cited by the statements about local zeta integrals of the $2 \times 2$ Godement section and their functional equations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_isSchwartzBruhat_matFourier22.lean

import Mathlib
import Definitions.Def_LanglandsTunnell_CubicInduction_GodementSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.isSchwartzBruhat_matFourier22
    (v : HeightOneSpectrum (𝓞 ℚ)) (η : AddChar (v.adicCompletion ℚ) ℂ) (n : ℤ)
    (hηn : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp n → η x = 1)
    (hηn' : ∃ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (n + 1) ∧ η x ≠ 1)
    (φ : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ) → ℂ) (hφ : IsSchwartzBruhat φ) :
    IsSchwartzBruhat (matFourier22 v η φ) := by sorry
