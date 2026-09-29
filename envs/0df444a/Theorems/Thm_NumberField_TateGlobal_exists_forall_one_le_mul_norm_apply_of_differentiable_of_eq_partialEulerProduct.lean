-- Prove2me | Theorems.Thm_NumberField_TateGlobal_exists_forall_one_le_mul_norm_apply_of_differentiable_of_eq_partialEulerProduct
-- name    : NumberField.TateGlobal.exists_forall_one_le_mul_norm_apply_of_differentiable_of_eq_partialEulerProduct
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/93af8d93-80f8-5da2-87f5-3a9e12c210b0
-- title:
--   Polynomial lower bound for a partial Hecke L-function on Re w≥ 1
-- statement:
--   Let $K$ be a number field and let $\chi \colon (\mathbf{A}_K)^\times \to \mathbb{C}^\times$ be a group homomorphism from the units of the adele ring of $\mathcal{O}_K$ in $K$ to $\mathbb{C}^\times$, subject to four hypotheses: $\chi$ is an idele class character, in the sense that $\chi$ kills the image of $K^\times$ under the diagonal embedding; $\chi$ is continuous; $\chi$ is unitary, in the sense that $\|\chi(x)\| = 1$ for every idele unit $x$; and $\chi$ is non-trivial on `normOneIdeles K`, the kernel of the Haar character `distribHaarChar` of the adele ring, i.e. there is an $x$ in that subgroup with $\chi(x) \neq 1$. Let $T$ be a finite set of primes in the height one spectrum of $\mathcal{O}_K$, and let $L \colon \mathbb{C} \to \mathbb{C}$ be differentiable on all of $\mathbb{C}$ and such that, for every $s$ with $\operatorname{Re} s > 1$, $L(s)$ equals the convergent product over the primes $v \notin T$ of $\bigl(1 - c_v\,N(v)^{-s}\bigr)^{-1}$, where $N(v) = \mathrm{absNorm}$ of the ideal of $v$, and where $c_v = \chi(\mathtt{uniformizerIdele}\ K\ v)$ — the value of $\chi$ at the idele which is trivial at all places other than $v$ and is a uniformiser of the completion $K_v$ at $v$ — if $\chi$ is unramified at $v$, meaning that the local character $\chi \circ \mathrm{finIncl} \circ \mathrm{localUnit}_v$ on $K_v^\times$ takes the value $1$ at every $t$ with both $t$ and $t^{-1}$ in the valuation ring of $K_v$, and $c_v = 0$ otherwise. The conclusion is that there exist a real number $A$ and a natural number $N$ with $1 \le A\,(1+|\operatorname{Im} w|)^N\,\|L(w)\|$ for every $w$ with $\operatorname{Re} w \ge 1$.
--
--   This is the non-vanishing of a Hecke $L$-function on the closed half-plane $\operatorname{Re} w \ge 1$, in the quantitative form of a polynomial lower bound, here for the partial Euler product omitting a finite set $T$ of primes and for a unitary idele class character that is non-trivial on the norm-one ideles; equivalently, $1/L$ grows at most polynomially in $|\operatorname{Im} w|$ on that region. It is used in the analytic continuation and polynomial bounding of regularised intertwining integrals of induced sections.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_TateGlobal_exists_forall_one_le_mul_norm_apply_of_differentiable_of_eq_partialEulerProduct.lean

import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_HeckeEigenfunction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain AutomorphicForm
open NumberField.TateGlobal
open scoped Classical in

theorem NumberField.TateGlobal.exists_forall_one_le_mul_norm_apply_of_differentiable_of_eq_partialEulerProduct
    (K : Type) [Field K] [NumberField K]
    (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (_hχ : IsIdeleClassChar (𝓞 K) K χ) (_hχc : Continuous χ)
    (_hχu : IsUnitaryChar (𝓞 K) K χ)
    (_hχ1 : ∃ x ∈ normOneIdeles K, χ x ≠ 1)
    (T : Finset (HeightOneSpectrum (𝓞 K)))
    (L : ℂ → ℂ) (_hL : Differentiable ℂ L)
    (_hLE : ∀ s : ℂ, 1 < s.re →
        L s = ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
          (1 - (if IsUnramifiedCharAt χ v.1 then ((χ (uniformizerIdele K v.1) : ℂˣ) : ℂ) else 0) *
            (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹) :
    ∃ (A : ℝ) (N : ℕ), ∀ w : ℂ, 1 ≤ w.re → 1 ≤ A * (1 + |w.im|) ^ N * ‖L w‖ := by sorry
