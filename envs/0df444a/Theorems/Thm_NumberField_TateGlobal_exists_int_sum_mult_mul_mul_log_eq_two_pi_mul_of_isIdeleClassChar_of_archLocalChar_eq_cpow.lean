-- Prove2me | Theorems.Thm_NumberField_TateGlobal_exists_int_sum_mult_mul_mul_log_eq_two_pi_mul_of_isIdeleClassChar_of_archLocalChar_eq_cpow
-- name    : NumberField.TateGlobal.exists_int_sum_mult_mul_mul_log_eq_two_pi_mul_of_isIdeleClassChar_of_archLocalChar_eq_cpow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/6a391595-80b0-52ac-b1f3-bed7732f9016
-- title:
--   Unit relation for archimedean parameters of unramified idele class characters
-- statement:
--   Let $K$ be a number field, and let $\chi\colon(\mathbb{A}_K)^\times\to\mathbb{C}^\times$ be a group homomorphism on the units of the adele ring of $\mathcal{O}_K$ in $K$ whose underlying complex-valued function is continuous, which is an idele class character in the sense that $\chi$ kills the image of $K^\times$ under the diagonal map $K\to\mathbb{A}_K$, and which is unramified at every place $v$ of the height-one spectrum of $\mathcal{O}_K$, meaning that $\chi$ takes the value $1$ on every idele obtained by placing at $v$ a unit $t$ of the completion $K_v$ such that both $t$ and $t^{-1}$ lie in the valuation ring of $K_v$. Let $\sigma\colon\{v\mid\infty\}\to\mathbb{R}$ be a family of real numbers indexed by the infinite places of $K$, and assume that for every infinite place $v$ and every $x\in(K_v)^\times$ the value of $\chi$ at the idele with component $x$ at $v$, component $1$ at the other infinite places and trivial finite part equals $\|\cdot\|^{\,\sigma_v i}$ evaluated at the idele norm of that idele, the idele norm being the scaling factor of Haar measure on $\mathbb{A}_K$ under multiplication. Then for every unit $\varepsilon\in\mathcal{O}_K^\times$ there is an integer $n$ with $\sum_{v\mid\infty}\mathrm{mult}(v)\,\sigma_v\log v(\varepsilon)=2\pi n$, where $\mathrm{mult}(v)$ is $1$ at a real place and $2$ at a complex place.
--
--   This is the classical relation expressing that the archimedean parameter vector $(\sigma_v)$ of a continuous idele class character that is unramified everywhere at the finite places pairs into $2\pi\mathbb{Z}$ with Dirichlet's log-unit lattice, the coordinates of the lattice being $\mathrm{mult}(v)\log|\varepsilon|_v$. It is used in the analysis of unitary Hecke characters of level one, where it bounds the possible archimedean parameters, and feeds into the finiteness and spacing statement for such characters.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_TateGlobal_exists_int_sum_mult_mul_mul_log_eq_two_pi_mul_of_isIdeleClassChar_of_archLocalChar_eq_cpow.lean

import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain AutomorphicForm

theorem NumberField.TateGlobal.exists_int_sum_mult_mul_mul_log_eq_two_pi_mul_of_isIdeleClassChar_of_archLocalChar_eq_cpow
    (K : Type) [Field K] [NumberField K]
    (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (hχc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ z : ℂˣ) : ℂ))
    (hχic : IsIdeleClassChar (𝓞 K) K χ)
    (hram : ∀ v : HeightOneSpectrum (𝓞 K), NumberField.TateGlobal.IsUnramifiedCharAt χ v)
    (σ : InfinitePlace K → ℝ)
    (hσ : ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
      ((NumberField.TateGlobal.archLocalChar χ v x : ℂˣ) : ℂ) =
        (((NumberField.TateGlobal.ideleNorm K (NumberField.TateGlobal.archUnitHom v x)) : ℝ) : ℂ) ^
          (((σ v : ℝ) : ℂ) * Complex.I))
    (ε : (𝓞 K)ˣ) :
    ∃ n : ℤ, ∑ v : InfinitePlace K, (v.mult : ℝ) * σ v * Real.log (v (((ε : 𝓞 K)) : K)) = 2 * Real.pi * n := by sorry
