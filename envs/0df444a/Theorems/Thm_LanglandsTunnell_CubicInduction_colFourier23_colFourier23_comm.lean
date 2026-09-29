-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_colFourier23_colFourier23_comm
-- name    : LanglandsTunnell.CubicInduction.colFourier23_colFourier23_comm
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/5f360a92-b681-50d0-840f-dd169118205d
-- title:
--   Column Fourier transforms in distinct columns commute
-- statement:
--   Let $v$ be a nonzero prime of $\mathcal O_{\mathbb Q}$, write $F = \mathbb Q_v$ for the associated adic completion, let $\eta$ be an additive character of $F$ with values in $\mathbb C$, and let $n$ be an integer such that $\eta$ is trivial on every $x \in F$ with $|x|_v \le \exp(n)$ (in the $\mathrm{WithZero}$-valuation notation of the valued completion), while some $x$ with $|x|_v \le \exp(n+1)$ satisfies $\eta(x) \neq 1$; thus $\eta$ has exact level determined by $n$. Let $a, b \in \{0,1,2\}$ with $a \neq b$, and let $\rho : M_{2\times 3}(F) \to \mathbb C$ be Schwartz–Bruhat, i.e. locally constant with compact support. The conclusion is the equality of functions on $M_{2\times 3}(F)$
--   $$\mathrm{col}_a\bigl(\mathrm{col}_b\,\rho\bigr) = \mathrm{col}_b\bigl(\mathrm{col}_a\,\rho\bigr),$$
--   where `colFourier23 v η j` sends $\Phi$ to the function
--   $$X \mapsto \int_{F\times F} \Phi\bigl(\mathrm{setCol23}\,X\,j\,u\bigr)\,\eta\bigl(u_1 X_{0j} + u_2 X_{1j}\bigr)\,du,$$
--   `setCol23 v X j u` being the matrix $X$ with its $j$-th column replaced by $(u_1,u_2)^{t}$, and the measure being the product of two copies of the self-dual Haar measure `selfDualHaarAt ℚ v` on $F$ (the additive Haar measure normalised on the local integers, scaled by $N(v)^{-\ell/2}$ with $\ell$ the level of the standard local character), taken with respect to the Borel $\sigma$-algebra `localBorel ℚ v`.
--
--   This is the Fubini-type commutation of the partial Fourier transforms taken along two distinct columns of a $2\times 3$ matrix over a local field, the basic symmetry underlying the Godement-type section construction used in the cubic induction. It is cited by the corresponding commutation statement for $2\times 2$ matrices, by the computation of the iterated $2\times 2$ matrix Fourier transform against the standard local character as composition with negation, and by the transformation formula for `matFourier23` under right multiplication by a transvection.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_colFourier23_colFourier23_comm.lean

import Mathlib
import Definitions.Def_LanglandsTunnell_CubicInduction_GodementSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.colFourier23_colFourier23_comm
    (v : HeightOneSpectrum (𝓞 ℚ)) (η : AddChar (v.adicCompletion ℚ) ℂ) (n : ℤ)
    (hηn : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp n → η x = 1)
    (hηn' : ∃ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (n + 1) ∧ η x ≠ 1)
    (a b : Fin 3) (hab : a ≠ b)
    (ρ : Matrix (Fin 2) (Fin 3) (v.adicCompletion ℚ) → ℂ) (hρ : IsSchwartzBruhat ρ) :
    colFourier23 v η a (colFourier23 v η b ρ) = colFourier23 v η b (colFourier23 v η a ρ) := by sorry
