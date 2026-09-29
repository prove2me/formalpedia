-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_whittakerFunctional3_spherical_ne_zero_of_norm_eq_one
-- name    : LanglandsTunnell.CubicInduction.whittakerFunctional3_spherical_ne_zero_of_norm_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/437b6ac2-c30f-5eb5-8c40-ff4fcef4f574
-- title:
--   Whittaker functionals do not vanish on the spherical vector
-- statement:
--   Let $v$ be a nonzero prime of the ring of integers of $\mathbb{Q}$, with completion $\mathbb{Q}_v$ carrying its valuation and norm, and let $\chi : \mathrm{Fin}\,3 \to \mathrm{Hom}(\mathbb{Q}_v^{\times},\mathbb{C}^{\times})$ be a triple of characters such that each $\chi_i$ is trivial on every unit of norm $1$ (hypothesis `hχ`) and takes values of complex modulus $1$ (hypothesis `hχu`). Let $f$ belong to the submodule `principalSeries3 v χ` of functions $\mathrm{GL}_3(\mathbb{Q}_v) \to \mathbb{C}$, that is: $f$ is locally constant, satisfies $f(u(x,y,z)g) = f(g)$ for the upper unipotent matrices $u(x,y,z) = \left(\begin{smallmatrix}1&x&z\\0&1&y\\0&0&1\end{smallmatrix}\right)$, and satisfies $f(\mathrm{diag}(a_0,a_1,a_2)\,g) = \bigl(\prod_{i}\chi_i(a_i)\bigr)\,\bigl(\|a_0\|/\|a_2\|\bigr)\,f(g)$ for all unit triples $a$ (note that the modulus factor is $\|a_0\|/\|a_2\|$ itself, not a square root). Assume $f(1) = 1$ and that $f$ is right invariant under the subgroup `localMaximalCompact3` of those $k \in \mathrm{GL}_3(\mathbb{Q}_v)$ all of whose entries and all of whose inverse's entries have valuation $\le 1$, in the sense $f(gk) = f(g)$. Let $\psi_v$ be an additive character of $\mathbb{Q}_v$ with $\psi_v(x) = 1$ whenever $\mathrm{v}(x) \le 1$, and with $\psi_v(x) \neq 1$ for some $x$ with $\mathrm{v}(x) \le \mathrm{exp}(1)$. Finally let $\Lambda$ be a nonzero $\mathbb{C}$-linear functional on `principalSeries3 v χ` satisfying $\Lambda(F \circ (\,\cdot\, u(x,y,z))) = \psi_v(x+y)\,\Lambda(F)$ for all $x,y,z$ and all $F$. Then $\Lambda f \neq 0$.
--
--   This is the non-vanishing half of the Casselman–Shalika formula for $\mathrm{GL}_3$ over a $p$-adic field: the value of a $\psi_v$-Whittaker functional at the normalised spherical vector of an unramified unitary principal series is nonzero. It feeds the identification of Hecke eigenfunctions with coefficient functions of `principalSeries3`, used in `exists_eq_coefficientFn_principalSeries3_of_isCosetEigenfunction_of_norm_eq_one`; the argument appeals to the Iwasawa-type decomposition $g = u(x,y,z)\,t\,k$ with $t$ diagonal and $k$ in the maximal compact, and to uniqueness up to scalars of Whittaker functionals on `principalSeries3`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_whittakerFunctional3_spherical_ne_zero_of_norm_eq_one.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries3

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField
open LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.whittakerFunctional3_spherical_ne_zero_of_norm_eq_one
    (v : HeightOneSpectrum (𝓞 ℚ)) (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (hχ : ∀ (i : Fin 3) (x : (v.adicCompletion ℚ)ˣ), ‖(x : v.adicCompletion ℚ)‖ = 1 → χ i x = 1)
    (hχu : ∀ (i : Fin 3) (x : (v.adicCompletion ℚ)ˣ), ‖((χ i x : ℂˣ) : ℂ)‖ = 1)
    (f : ↥(principalSeries3 v χ)) (hf1 : (f : LocalGL3 v → ℂ) 1 = 1)
    (hfK : IsRightInvariant (localMaximalCompact3 (𝓞 ℚ) ℚ v) (f : LocalGL3 v → ℂ))
    (ψv : AddChar (v.adicCompletion ℚ) ℂ)
    (hψ0 : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ 1 → ψv x = 1)
    (hψ1 : ∃ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (1 : ℤ) ∧ ψv x ≠ 1)
    (Λ : ↥(principalSeries3 v χ) →ₗ[ℂ] ℂ) (hΛ : IsWhittakerFunctional3 ψv Λ) (hΛne : Λ ≠ 0) :
    Λ f ≠ 0 := by sorry
