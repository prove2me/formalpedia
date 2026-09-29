-- Prove2me | Theorems.Thm_NumberField_TateGlobal_exists_forall_norm_partialEulerProduct_continuation_le_rpow_of_re_mem_Icc_of_admitsModulus
-- name    : NumberField.TateGlobal.exists_forall_norm_partialEulerProduct_continuation_le_rpow_of_re_mem_Icc_of_admitsModulus
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/987c5044-2311-5763-9377-71573ed7a2ee
-- title:
--   Convexity bound for partial Hecke L-functions in a strip
-- statement:
--   Let $K$ be a number field, $T$ a finite set of finite places of $K$ (nonzero primes of $\mathcal O_K$) and $\mathfrak f$ an ideal of $\mathcal O_K$. The assertion is that there exist real constants $C>0$ and $A>0$, depending only on $K$, $T$ and $\mathfrak f$, such that the following holds for every continuous group homomorphism $\chi\colon \mathbb A_K^\times\to\mathbb C^\times$ which is trivial on the image of $K^\times$, satisfies $\|\chi(x)\|=1$ for all ideles $x$, is nontrivial on the norm-one ideles (the kernel of the module character `distribHaarChar` of $\mathbb A_K$), admits $\mathfrak f$ as a modulus (i.e. $\chi(u)=1$ for every unit idele $u$ whose infinite component is $1$ and whose finite components satisfy $v(u_v)=1$ and $v(u_v-1)\le \exp(-m_v)$ at every finite place $v$, with $m_v$ the multiplicity of $v$ in $\mathfrak f$), and is unramified at every $v\notin T$ in the sense that the local character $\chi\circ$ (inclusion of $(K_v)^\times$ at $v$) is trivial on those $t$ with $t$ and $t^{-1}$ in the valuation ring; and for all families $\varphi\colon w\mapsto\varphi_w\in\mathbb R$ and $k\colon w\mapsto k_w\in\mathbb Z$ indexed by the infinite places, such that, via the embedding of $K_w$ in $\mathbb C$, the archimedean local character $\chi_w$ (i.e. $\chi$ composed with the inclusion of $(K_w)^\times$ at $w$) satisfies $\chi_w(a)=r^{\,i\varphi_w}$ whenever $a$ maps to a real $r>0$ and $\chi_w(a)=a^{k_w}$ whenever $\|a\|=1$; and for every $L\colon\mathbb C\to\mathbb C$ differentiable on all of $\mathbb C$ with $L(s)=\prod_{v\notin T}\bigl(1-c_v N(v)^{-s}\bigr)^{-1}$ for $\operatorname{Re}s>1$, where $c_v=\chi(\varpi_v)$ for the idele with uniformizer at $v$ and $1$ elsewhere if $\chi$ is unramified at $v$ and $c_v=0$ otherwise, and $N(v)$ is the absolute norm of $v$: for every $s$ with $-1/2\le\operatorname{Re}s\le 5/2$, $$\|L(s)\|\le C\Bigl(2+|\operatorname{Im}s|+\sum_{w\mid\infty}\bigl(|\varphi_w|+|k_w|\bigr)\Bigr)^{A}.$$
--
--   This is the convexity (Phragmén–Lindelöf) bound for partial Hecke $L$-functions throughout the closed strip $-1/2\le\operatorname{Re}s\le5/2$, polynomial in the height and in the archimedean parameters at fixed finite modulus. It is the growth input to the de la Vallée-Poussin type zero-free region for Hecke $L$-functions, and is cited by the statements producing a zero-free half-plane beyond $\operatorname{Re}s=1-c/\log(\cdot)$ and the accompanying bounds on $L'/L$ and $1/L$ there; the proof combines the bound on the line $\operatorname{Re}s=-1/2$, the Euler-product bound for $\operatorname{Re}s\ge1$, and the Phragmén–Lindelöf principle in a vertical strip.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_TateGlobal_exists_forall_norm_partialEulerProduct_continuation_le_rpow_of_re_mem_Icc_of_admitsModulus.lean

import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_HeckeEigenfunction
import Definitions.Def_HeckeCharacter_FiniteOrder

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain AutomorphicForm NumberField.TateGlobal NumberField.InfinitePlace

open scoped Classical in

theorem NumberField.TateGlobal.exists_forall_norm_partialEulerProduct_continuation_le_rpow_of_re_mem_Icc_of_admitsModulus
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
      ∀ s : ℂ, -1 / 2 ≤ s.re → s.re ≤ 5 / 2 →
        ‖L s‖ ≤ C * (2 + |s.im| + ∑ w : InfinitePlace K, (|φ w| + |(k w : ℝ)|)) ^ A := by sorry
