-- Prove2me | Theorems.Thm_NumberField_TateGlobal_exists_norm_partialEulerProduct_continuation_le_mul_exp_mul_im_sq
-- name    : NumberField.TateGlobal.exists_norm_partialEulerProduct_continuation_le_mul_exp_mul_im_sq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.964832+00:00
-- url     : https://prove2.me/theorems/5974f97f-f0f0-52a1-ab22-c2c6be4c45fa
-- title:
--   Vertical-strip Gaussian bound for a partial Hecke L-function
-- statement:
--   Let $K$ be a number field and let $\chi\colon \mathbb{A}_K^\times \to \mathbb{C}^\times$ be a homomorphism of the unit group of the adele ring of $\mathcal{O}_K$ in $K$ to $\mathbb{C}^\times$ which is continuous, trivial on the image of $K^\times$ under the diagonal embedding (`IsIdeleClassChar`), unitary in the sense that $\lVert\chi(x)\rVert = 1$ for every idele $x$ (`IsUnitaryChar`), and non-trivial on the norm-one ideles, i.e. there is an $x$ in the kernel of the module character `distribHaarChar` of $\mathbb{A}_K$ with $\chi(x)\neq 1$. Let $T$ be a finite set of height-one primes of $\mathcal{O}_K$, and let $L\colon\mathbb{C}\to\mathbb{C}$ be an entire function (differentiable on all of $\mathbb{C}$) which for every $s$ with $\operatorname{Re} s > 1$ is given by the partial Euler product $L(s) = \prod_{v\notin T}\bigl(1 - c_v\,N(v)^{-s}\bigr)^{-1}$ over the height-one primes $v$ outside $T$, where $N(v)$ is the absolute norm of $v$, and $c_v = \chi(\varpi_v)$ if $\chi$ is unramified at $v$ — meaning that the local character $t\mapsto\chi$ of the idele supported at $v$ with entry $t$ is trivial on all $t$ with both $t$ and $t^{-1}$ in the valuation ring of the completion $K_v$ — and $c_v = 0$ otherwise; here $\varpi_v$ is the idele equal to a fixed uniformizer at $v$ and to $1$ at all other places, archimedean places included. Then for all real numbers $a$, $b$ there exist real constants $B$ and $C$ such that $\lVert L(s)\rVert \le B\exp(C(\operatorname{Im} s)^2)$ for every $s$ with $a\le \operatorname{Re} s\le b$.
--
--   This is the a priori growth estimate — finite order in vertical strips, in the weak Gaussian form $B e^{Ct^2}$ with constants depending on $\chi$ — for the entire continuation of the Hecke $L$-function of a unitary idele class character that is non-trivial on the norm-one ideles, with the Euler factors at a finite set of primes removed. It is the hypothesis under which the Phragmén–Lindelöf principle converts bounds on two vertical lines into a bound on the strip between them, and it feeds the polynomial-growth statement [`NumberField.TateGlobal.exists_forall_norm_partialEulerProduct_continuation_le_rpow_of_re_mem_Icc_of_admitsModulus`](thm.html#NumberField.TateGlobal.exists_forall_norm_partialEulerProduct_continuation_le_rpow_of_re_mem_Icc_of_admitsModulus) used in the converse-theorem input to Langlands–Tunnell.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_TateGlobal_exists_norm_partialEulerProduct_continuation_le_mul_exp_mul_im_sq.lean

import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_HeckeEigenfunction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain AutomorphicForm NumberField.TateGlobal

open scoped Classical in

theorem NumberField.TateGlobal.exists_norm_partialEulerProduct_continuation_le_mul_exp_mul_im_sq
    (K : Type) [Field K] [NumberField K]
    (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hχ : IsIdeleClassChar (𝓞 K) K χ) (hχc : Continuous χ)
    (hχu : IsUnitaryChar (𝓞 K) K χ) (hχ1 : ∃ x ∈ normOneIdeles K, χ x ≠ 1)
    (T : Finset (HeightOneSpectrum (𝓞 K)))
    (L : ℂ → ℂ) (hL : Differentiable ℂ L)
    (hLT : ∀ s : ℂ, 1 < s.re →
      L s = ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
        (1 - (if IsUnramifiedCharAt χ v.1 then ((χ (uniformizerIdele K v.1) : ℂˣ) : ℂ) else 0) *
          (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹)
    (a b : ℝ) :
    ∃ B C : ℝ, ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖L s‖ ≤ B * Real.exp (C * s.im ^ 2) := by sorry
