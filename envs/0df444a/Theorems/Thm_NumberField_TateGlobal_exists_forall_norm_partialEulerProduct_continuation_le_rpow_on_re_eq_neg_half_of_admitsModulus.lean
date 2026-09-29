-- Prove2me | Theorems.Thm_NumberField_TateGlobal_exists_forall_norm_partialEulerProduct_continuation_le_rpow_on_re_eq_neg_half_of_admitsModulus
-- name    : NumberField.TateGlobal.exists_forall_norm_partialEulerProduct_continuation_le_rpow_on_re_eq_neg_half_of_admitsModulus
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/c874af1c-f74c-521d-aaa7-488617f8f938
-- title:
--   Polynomial bound on Re s=-1/2 for partial Hecke L-functions
-- statement:
--   Let $K$ be a number field, $T$ a finite set of nonzero primes of $\mathcal O_K$ and $\mathfrak f$ an ideal of $\mathcal O_K$. Then there are reals $C>0$ and $A>0$, depending only on these data, with the following property. Let $\chi\colon(\mathbb A_K)^\times\to\mathbb C^\times$ be a group homomorphism that is trivial on the image of $K^\times$, continuous, satisfies $\|\chi(x)\|=1$ for all ideles $x$, is nontrivial somewhere on `normOneIdeles K` (the kernel of the module character `distribHaarChar` of $\mathbb A_K$), admits the modulus $\mathfrak f$ in the sense that $\chi(u)=1$ whenever the infinite component of $u$ is $1$ and every finite component satisfies $v(u_v)=1$ and $v(u_v-1)\le\exp(-m_v)$ with $m_v$ the multiplicity of $v$ in $\mathfrak f$, and is unramified at every $v\notin T$, meaning that the local character $t\mapsto\chi$ of the idele equal to $t$ at $v$ and $1$ elsewhere is trivial on those $t$ with $t$ and $t^{-1}$ both integral. Let $\varphi\colon\Sigma_\infty\to\mathbb R$ and $k\colon\Sigma_\infty\to\mathbb Z$ be such that, for every infinite place $w$, the local character $a\mapsto\chi(\mathrm{archUnitHom}_w(a))$ on $(K_w)^\times$ sends a unit embedding to $r^{i\varphi_w}$ whenever its image in $\mathbb C$ is a real $r>0$, and to $u^{k_w}$ whenever that image $u$ has absolute value $1$. Let $L\colon\mathbb C\to\mathbb C$ be entire and equal, for $\operatorname{Re} s>1$, to the product over the primes $v\notin T$ of $(1-c_v N(v)^{-s})^{-1}$, where $c_v=\chi(\varpi_v)$ for the idele that is a uniformizer at $v$ and $1$ elsewhere if $\chi$ is unramified at $v$, and $c_v=0$ otherwise, and $N(v)$ is the absolute norm of $v$. Then for every $s$ with $\operatorname{Re} s=-1/2$,
--   $$\|L(s)\|\le C\Bigl(2+|\operatorname{Im} s|+\sum_{w\mid\infty}\bigl(|\varphi_w|+|k_w|\bigr)\Bigr)^{A}.$$
--
--   This is the functional-equation side of the convexity estimate for Hecke $L$-functions of unitary idele class characters: on the line $\operatorname{Re} s=-1/2$ the analytic continuation of the Euler product over the places outside $T$ grows at most polynomially in the archimedean data, uniformly over all characters of modulus dividing $\mathfrak f$ that are unramified outside $T$. It feeds the interpolated bound on a vertical strip, [`NumberField.TateGlobal.exists_forall_norm_partialEulerProduct_continuation_le_rpow_of_re_mem_Icc_of_admitsModulus`](thm.html#NumberField.TateGlobal.exists_forall_norm_partialEulerProduct_continuation_le_rpow_of_re_mem_Icc_of_admitsModulus).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_TateGlobal_exists_forall_norm_partialEulerProduct_continuation_le_rpow_on_re_eq_neg_half_of_admitsModulus.lean

import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_HeckeEigenfunction
import Definitions.Def_HeckeCharacter_FiniteOrder

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain AutomorphicForm NumberField.TateGlobal NumberField.InfinitePlace

open scoped Classical in

theorem NumberField.TateGlobal.exists_forall_norm_partialEulerProduct_continuation_le_rpow_on_re_eq_neg_half_of_admitsModulus
    (K : Type) [Field K] [NumberField K]
    (T : Finset (HeightOneSpectrum (𝓞 K))) (𝔣 : Ideal (𝓞 K)) :
    ∃ C A : ℝ, 0 < C ∧ 0 < A ∧
      ∀ (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ), IsIdeleClassChar (𝓞 K) K χ → Continuous χ →
        IsUnitaryChar (𝓞 K) K χ → (∃ x ∈ normOneIdeles K, χ x ≠ 1) →
        HeckeCharacter.AdmitsModulus K χ 𝔣 → (∀ v ∉ T, IsUnramifiedCharAt χ v) →
      ∀ (φ : InfinitePlace K → ℝ) (k : InfinitePlace K → ℤ),
        (∀ (w : InfinitePlace K) (a : (w.Completion)ˣ) (r : ℝ), 0 < r →
            Completion.extensionEmbedding w (a : w.Completion) = (r : ℂ) →
            ((archLocalChar χ w a : ℂˣ) : ℂ) = (r : ℂ) ^ (Complex.I * φ w)) →
        (∀ (w : InfinitePlace K) (a : (w.Completion)ˣ),
            ‖Completion.extensionEmbedding w (a : w.Completion)‖ = 1 →
            ((archLocalChar χ w a : ℂˣ) : ℂ) = (Completion.extensionEmbedding w (a : w.Completion)) ^ (k w)) →
      ∀ (L : ℂ → ℂ), Differentiable ℂ L →
        (∀ s : ℂ, 1 < s.re → L s = ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
            (1 - (if IsUnramifiedCharAt χ v.1 then ((χ (uniformizerIdele K v.1) : ℂˣ) : ℂ) else 0) *
              (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹) →
      ∀ s : ℂ, s.re = -1 / 2 →
        ‖L s‖ ≤ C * (2 + |s.im| + ∑ w : InfinitePlace K, (|φ w| + |(k w : ℝ)|)) ^ A := by sorry
