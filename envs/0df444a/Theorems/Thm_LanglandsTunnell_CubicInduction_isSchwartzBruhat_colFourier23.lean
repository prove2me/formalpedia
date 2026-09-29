-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_isSchwartzBruhat_colFourier23
-- name    : LanglandsTunnell.CubicInduction.isSchwartzBruhat_colFourier23
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/7eaca978-bdf4-52ee-b85a-d5bf0b13917d
-- title:
--   Column Fourier transform preserves Schwartz–Bruhat functions
-- statement:
--   Let $v$ be a height-one prime of the ring of integers of $\mathbb{Q}$, with completion $F = \mathbb{Q}_v$ carried by its Borel $\sigma$-algebra `localBorel`, and let $\eta$ be an additive character $F \to \mathbb{C}^\times$. Let $n$ be an integer and assume two conditions pinning down the level of $\eta$: $\eta(x) = 1$ for every $x$ with $\mathrm{val}(x) \le \exp(n)$, and there exists some $x$ with $\mathrm{val}(x) \le \exp(n+1)$ and $\eta(x) \ne 1$. Let $j \in \{0,1,2\}$ be a column index and let $\Phi : M_{2\times 3}(F) \to \mathbb{C}$ be Schwartz–Bruhat in the sense of this development, i.e. locally constant and of compact support. The conclusion is that the $j$-th column transform of $\Phi$ is again locally constant with compact support, where that transform sends a matrix $X$ to $$\int_{F \times F} \Phi\big(\mathrm{setCol23}(X,j,u)\big)\, \eta\big(u_1 X_{0j} + u_2 X_{1j}\big)\, d(\mu_v \otimes \mu_v)(u),$$ with $\mathrm{setCol23}(X,j,u)$ the matrix obtained from $X$ by replacing its $j$-th column by $(u_1,u_2)^{T}$ and leaving the other two columns untouched, and $\mu_v =$ `selfDualHaarAt` the additive Haar measure on $F$ normalised by the factor $(\#\mathcal{O}/v)^{-\mathrm{level}(\psi_v)/2}$ on the ring of integers.
--
--   This is the stability of the space of Schwartz–Bruhat functions on $2\times 3$ matrices over a local field under the partial Fourier transform in the two variables forming one column, as used in the Godement-section construction of local zeta integrals. It is deduced from the one-variable local statement [`LanglandsTunnell.TateLocal.isSchwartzBruhat_tateFourier`](thm.html#LanglandsTunnell.TateLocal.isSchwartzBruhat_tateFourier), and is in turn invoked in the treatment of the matrix Fourier transforms and their commutation and duality properties.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_isSchwartzBruhat_colFourier23.lean

import Mathlib
import Definitions.Def_LanglandsTunnell_CubicInduction_GodementSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.isSchwartzBruhat_colFourier23
    (v : HeightOneSpectrum (𝓞 ℚ)) (η : AddChar (v.adicCompletion ℚ) ℂ) (n : ℤ)
    (hηn : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp n → η x = 1)
    (hηn' : ∃ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (n + 1) ∧ η x ≠ 1)
    (j : Fin 3) (Φ : Matrix (Fin 2) (Fin 3) (v.adicCompletion ℚ) → ℂ) (hΦ : IsSchwartzBruhat Φ) :
    IsSchwartzBruhat (colFourier23 v η j Φ) := by sorry
