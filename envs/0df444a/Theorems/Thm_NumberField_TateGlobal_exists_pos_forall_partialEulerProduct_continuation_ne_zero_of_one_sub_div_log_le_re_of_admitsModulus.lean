-- Prove2me | Theorems.Thm_NumberField_TateGlobal_exists_pos_forall_partialEulerProduct_continuation_ne_zero_of_one_sub_div_log_le_re_of_admitsModulus
-- name    : NumberField.TateGlobal.exists_pos_forall_partialEulerProduct_continuation_ne_zero_of_one_sub_div_log_le_re_of_admitsModulus
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.964832+00:00
-- url     : https://prove2.me/theorems/838597ed-70e9-5244-82cd-0627b4c8f820
-- title:
--   De la Vallée Poussin zero-free region for partial Hecke L-functions
-- statement:
--   Let $K$ be a number field, $T$ a finite set of height-one primes of $\mathcal O_K$ and $\mathfrak f$ an ideal of $\mathcal O_K$. Then there is a real $c>0$, depending only on these data, with the following property. Let $\chi \colon (\mathbb A_K)^\times \to \mathbb C^\times$ be a continuous group homomorphism which is trivial on the image of $K^\times$, satisfies $\|\chi(x)\|=1$ for every idele unit $x$, is non-trivial somewhere on the kernel of the distributive Haar character of $\mathbb A_K$ (the norm-one ideles), admits $\mathfrak f$ as modulus, i.e. $\chi(u)=1$ whenever the infinite component of $u$ is $1$ and every finite component satisfies $v(u_v)=1$ and $v(u_v-1)\le \exp(-m_v)$ with $m_v$ the multiplicity of $v$ in $\mathfrak f$, and is unramified at each $v \notin T$, meaning that the local character $\chi \circ \mathrm{localUnit}$ at $v$ is trivial on all $t$ with $t$ and $t^{-1}$ integral. Let $\varphi \colon$ (infinite places) $\to \mathbb R$ and $k \colon$ (infinite places) $\to \mathbb Z$ be such that, for every infinite place $w$ and every $a \in (K_w)^\times$, the value of $\chi$ on the idele supported at $w$ with entry $a$ equals $r^{i\varphi_w}$ when the embedding of $a$ into $\mathbb C$ is a real $r>0$, and equals $a^{k_w}$ when that embedding has absolute value $1$. Finally let $L \colon \mathbb C \to \mathbb C$ be entire with $L(s)=\prod'_{v \notin T}\bigl(1-c_v\,N(v)^{-s}\bigr)^{-1}$ for $\operatorname{Re} s>1$, where $c_v=\chi(\varpi_v)$ for the uniformizer idele at $v$ if $\chi$ is unramified at $v$ and $c_v=0$ otherwise, and $N(v)$ is the absolute norm of $v$. Then $L(s) \neq 0$ for every $s$ with $\operatorname{Re} s \ge 1 - c/\log\bigl(2+|\operatorname{Im} s|+\sum_w (|\varphi_w|+|k_w|)\bigr)$.
--
--   This is the de la Vallée Poussin type zero-free region for Hecke $L$-functions of unitary idele class characters, uniform in the height of $s$ and in the archimedean parameters $\varphi, k$ at fixed finite modulus $\mathfrak f$ and fixed excluded set $T$; characters of the form $\|\cdot\|^{i\tau}$, whose partial $L$-function is a translate of the partial Dedekind zeta function and has a pole, are excluded by the non-triviality requirement on the norm-one ideles. It feeds the statement combining this zero-free region with bounds for the logarithmic derivative and for the inverse of the partial Euler product continuation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_TateGlobal_exists_pos_forall_partialEulerProduct_continuation_ne_zero_of_one_sub_div_log_le_re_of_admitsModulus.lean

import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_HeckeEigenfunction
import Definitions.Def_HeckeCharacter_FiniteOrder

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain AutomorphicForm NumberField.TateGlobal NumberField.InfinitePlace

open scoped Classical in

theorem NumberField.TateGlobal.exists_pos_forall_partialEulerProduct_continuation_ne_zero_of_one_sub_div_log_le_re_of_admitsModulus
    (K : Type) [Field K] [NumberField K]
    (T : Finset (HeightOneSpectrum (𝓞 K))) (𝔣 : Ideal (𝓞 K)) :
    ∃ c : ℝ, 0 < c ∧
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
      ∀ s : ℂ, 1 - c / Real.log (2 + |s.im| + ∑ w : InfinitePlace K, (|φ w| + |(k w : ℝ)|)) ≤ s.re →
        L s ≠ 0 := by sorry
