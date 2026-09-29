-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_matFourier22_congr_of_forall_det_ne_zero
-- name    : LanglandsTunnell.CubicInduction.matFourier22_congr_of_forall_det_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/864b638c-3f97-5b2b-aead-a5ea5993e488
-- title:
--   Matrix Fourier transform sees only nonsingular matrices
-- statement:
--   Let $v$ be a point of the height one spectrum of the ring of integers of $\mathbb{Q}$, with completion $\mathbb{Q}_v$, let $\eta$ be an additive character of $\mathbb{Q}_v$ with values in $\mathbb{C}$, and let $\varphi,\varphi' : M_2(\mathbb{Q}_v)\to\mathbb{C}$ be arbitrary functions. Assume that $\varphi(X)=\varphi'(X)$ for every $X\in M_2(\mathbb{Q}_v)$ with $\det X\neq 0$. The conclusion is the equality of functions $M_2(\mathbb{Q}_v)\to\mathbb{C}$ given by `matFourier22 v η φ = matFourier22 v η φ'`, where `matFourier22 v η` is the composite of the two single-column transforms, namely `colFourier22 v η 0` applied to `colFourier22 v η 1`, and where for a column index $j$ and a function $\psi$ on $M_2(\mathbb{Q}_v)$ the value of `colFourier22 v η j ψ` at $X$ is the Bochner integral
--   $$\int_{\mathbb{Q}_v\times\mathbb{Q}_v} \psi\big(\mathrm{setCol22}\,v\,X\,j\,u\big)\,\eta\big(u_1 X_{0j}+u_2 X_{1j}\big)\,d\mu(u),$$
--   taken against the product of two copies of the self-dual Haar measure `selfDualHaarAt ℚ v` on $\mathbb{Q}_v$, with the local Borel structure `localBorel ℚ v`, the integrand being evaluated at the matrix `setCol22 v X j u` built from $X$ and the pair $u$ at column index $j$. No measurability or integrability hypothesis on $\varphi$ or $\varphi'$ is imposed.
--
--   This is the statement that the two-column (Godement-style) Fourier transform on $M_2(\mathbb{Q}_v)$ is insensitive to the values of a function on the singular locus, the latter being null for the iterated column integrals; it lets one replace a function by any modification of it off $\mathrm{GL}_2(\mathbb{Q}_v)$. It is used in [`LanglandsTunnell.RankinSelberg.matFourier22_kirillov_det_mul_coefficient_eq_of_cuspidal`](thm.html#LanglandsTunnell.RankinSelberg.matFourier22_kirillov_det_mul_coefficient_eq_of_cuspidal), in the comparison of Fourier–Kirillov coefficients for the two-variable Rankin–Selberg integral.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_matFourier22_congr_of_forall_det_ne_zero.lean

import Mathlib
import Definitions.Def_LanglandsTunnell_CubicInduction_GodementSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.matFourier22_congr_of_forall_det_ne_zero
    (v : HeightOneSpectrum (𝓞 ℚ)) (η : AddChar (v.adicCompletion ℚ) ℂ)
    (φ φ' : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ) → ℂ)
    (h : ∀ X : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ), X.det ≠ 0 → φ X = φ' X) :
    matFourier22 v η φ = matFourier22 v η φ' := by sorry
