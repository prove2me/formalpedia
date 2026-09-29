-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_matFourier22_comp_mul_right_eq
-- name    : LanglandsTunnell.CubicInduction.matFourier22_comp_mul_right_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/9dd817fd-fd5c-529f-aa97-712ffdb3a2a5
-- title:
--   Right translation covariance of the 2×2 matrix Fourier transform
-- statement:
--   Let $v$ be a nonzero prime ideal of the ring of integers of $\mathbb{Q}$, write $F = \mathbb{Q}_v$ for the $v$-adic completion, and let $\eta$ be an additive character of $F$ with values in $\mathbb{C}$. Let $n$ be an integer such that $\eta x = 1$ for every $x \in F$ with $\mathrm{v}(x) \le \exp(n)$, and such that there exists $x \in F$ with $\mathrm{v}(x) \le \exp(n+1)$ and $\eta x \ne 1$; thus $\eta$ is trivial on one valuation ball and non-trivial on the next, pinning down its level. Let $\Phi : M_2(F) \to \mathbb{C}$ be locally constant with compact support, let $a \in \mathrm{GL}_2(F)$ and let $Y \in M_2(F)$. Here `matFourier22 v η` is the iterated column transform $\mathrm{colFourier22}\,0 \circ \mathrm{colFourier22}\,1$, where the $j$-th column transform of $\varphi$ at $X$ is $\int_{F \times F} \varphi(X \text{ with column } j \text{ replaced by } u)\, \eta(u_1 X_{0j} + u_2 X_{1j})$ against the product of two copies of the self-dual Haar measure at $v$. The assertion is that the transform of $X \mapsto \Phi(Xa)$ evaluated at $Y$ equals $\big(\mathrm{modulus}(\det a)\big)^{-1}$ squared, viewed in $\mathbb{C}$, times the transform of $\Phi$ evaluated at $Y \cdot {}^{t}(a^{-1})$, the second factor being the matrix underlying `transposeInvN (Fin 2) a`. The modulus of a nonzero scalar is the scaling factor of Haar measure under multiplication by it.
--
--   This is the standard covariance of the matrix Fourier transform on $M_2(F)$ under right translation by $a \in \mathrm{GL}_2(F)$, the two-dimensional analogue of $\widehat{f(\cdot\,a)} = |\det a|^{-2}\hat f(\cdot\,{}^{t}a^{-1})$ used in the local theory of Godement sections and Tate integrals for $\mathrm{GL}_2$. It is invoked in the local Rankin–Selberg computations, both for the functional equation of the Godement zeta integral of the transform and for the identification of the transform against Kirillov coefficients of cuspidal representations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_matFourier22_comp_mul_right_eq.lean

import Mathlib
import Definitions.Def_LanglandsTunnell_CubicInduction_GodementSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.matFourier22_comp_mul_right_eq
    (v : HeightOneSpectrum (𝓞 ℚ)) (η : AddChar (v.adicCompletion ℚ) ℂ) (n : ℤ)
    (hηn : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp n → η x = 1)
    (hηn' : ∃ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (n + 1) ∧ η x ≠ 1)
    (Φ : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ) → ℂ) (hΦ : IsSchwartzBruhat Φ)
    (a : GL (Fin 2) (v.adicCompletion ℚ)) (Y : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) :
    matFourier22 v η (fun X => Φ (X * (a : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)))) Y =
      ((modulus ((Matrix.GeneralLinearGroup.det a : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ) : ℂ)⁻¹ ^ 2 *
        matFourier22 v η Φ (Y * ((transposeInvN (Fin 2) a : GL (Fin 2) (v.adicCompletion ℚ)) :
          Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))) := by sorry
