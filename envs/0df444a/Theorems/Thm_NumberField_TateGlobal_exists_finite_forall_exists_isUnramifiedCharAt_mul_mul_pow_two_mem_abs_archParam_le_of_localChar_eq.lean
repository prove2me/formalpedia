-- Prove2me | Theorems.Thm_NumberField_TateGlobal_exists_finite_forall_exists_isUnramifiedCharAt_mul_mul_pow_two_mem_abs_archParam_le_of_localChar_eq
-- name    : NumberField.TateGlobal.exists_finite_forall_exists_isUnramifiedCharAt_mul_mul_pow_two_mem_abs_archParam_le_of_localChar_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/fd5fda07-7711-560d-a32e-2f68c1f47bde
-- title:
--   Unramified twists normalising pairs of unitary Hecke characters
-- statement:
--   Let $K$ be a number field, $S_0$ a finite set of maximal ideals of $\mathcal O_K$, $\rho_1,\dots,\rho_{n_\rho}$ a finite list of families assigning to each finite place $v$ a character $(K_v)^\times\to\mathbb C^\times$, and $n_0\in\mathbb N$. The assertion is that there exist $B\ge 0$ and a finite set $\Xi$ of characters $(\mathbb A_K)^\times\to\mathbb C^\times$, each unitary ($\|\xi(x)\|=1$ for all ideles $x$), trivial on the principal ideles $K^\times$, and continuous as a $\mathbb C$-valued function, with the following property. Let $\mu,\nu$ be characters of $(\mathbb A_K)^\times$ that are unitary, trivial on $K^\times$, and continuous; assume each is unramified outside $S_0$, in the sense that for $v\notin S_0$ the local character $\mathrm{localChar}$ obtained by restricting along the embedding of $(K_v)^\times$ as the idele with entry at $v$ and $1$ elsewhere is trivial on all $u$ with $u,u^{-1}$ integral; assume further that for some indices $r,r'$ these local characters agree with $\rho_r(v)$, resp. $\rho_{r'}(v)$, on such $u$ for every $v\in S_0$. Let $\tau^\mu,\tau^\nu:\ \mathrm{InfinitePlace}(K)\to\mathbb R$ and $m^\mu,m^\nu:\ \mathrm{InfinitePlace}(K)\to\mathbb Z$ describe the archimedean components: for each infinite place $v$, the character $\mathrm{archLocalChar}$ of $(K_v)^\times$ (restriction of $\mu$ along $x\mapsto$ the idele with entry $x$ at $v$ and $1$ elsewhere) equals $\mathrm{ideleNorm}(\cdot)^{i\tau^\mu_v}$ on those $x$ whose image under the completion embedding is real and positive, and equals $x\mapsto(\text{image of }x)^{m^\mu_v}$ on those $x$ of absolute value $1$, and likewise for $\nu$; assume $m^\mu_v,m^\nu_v\in\{0,1\}$ at real places and $|m^\mu_v-m^\nu_v|\le n_0$ at complex places. Then there are a character $\eta$ of $(\mathbb A_K)^\times$ which is unitary, trivial on $K^\times$, continuous, and unramified at every finite place, together with archimedean parameters $\tau^\eta$ and weights $m^\eta$ for $\eta$ in the same sense, with $m^\eta_v=0$ at real places, such that $\mu\nu\eta^2\in\Xi$, $|\tau^\mu_v+\tau^\nu_v+2\tau^\eta_v|\le B$ and $|m^\mu_v+m^\eta_v|\le B$, $|m^\nu_v+m^\eta_v|\le B$ for all infinite $v$, and, for every $t\in\mathbb R$, $$1+\sum_v\bigl(|t+\tau^\mu_v+\tau^\eta_v|+|t-\tau^\nu_v-\tau^\eta_v|+|m^\mu_v+m^\eta_v|+|m^\nu_v+m^\eta_v|\bigr)\ \le\ B\Bigl(1+\sum_v|2t+\tau^\mu_v-\tau^\nu_v|\Bigr).$$ Here $\mathrm{ideleNorm}$ is the module of an idele, the scaling factor of Haar measure on $\mathbb A_K$.
--
--   This is a uniformity statement for Hecke characters: a pair of unitary idele class characters with prescribed ramification data can be twisted by an everywhere unramified unitary character so that the product $\mu\nu\eta^2$ lies in one fixed finite set, while the archimedean parameters of the twisted pair remain bounded in terms of the parameters of the quotient $\mu\nu^{-1}$. It is used in the analytic estimates for intertwining integrals attached to principal series, the existence of the unramified twist coming from the Hecke-type existence theorem [`NumberField.TateGlobal.exists_forall_exists_isIdeleClassChar_isUnramifiedCharAt_archLocalChar_eq_abs_sub_le`](thm.html#NumberField.TateGlobal.exists_forall_exists_isIdeleClassChar_isUnramifiedCharAt_archLocalChar_eq_abs_sub_le) and the finiteness from [`AutomorphicForm.exists_forall_finite_and_ncard_archParam_spread_le_of_isUnitaryChar_of_pairwise_ne_normOneIdeles`](thm.html#AutomorphicForm.exists_forall_finite_and_ncard_archParam_spread_le_of_isUnitaryChar_of_pairwise_ne_normOneIdeles).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_TateGlobal_exists_finite_forall_exists_isUnramifiedCharAt_mul_mul_pow_two_mem_abs_archParam_le_of_localChar_eq.lean

import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain
open AutomorphicForm

theorem NumberField.TateGlobal.exists_finite_forall_exists_isUnramifiedCharAt_mul_mul_pow_two_mem_abs_archParam_le_of_localChar_eq
    (K : Type) [Field K] [NumberField K]
    (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
    (nρ : ℕ) (ρs : Fin nρ → ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ) (n₀ : ℕ) :
    ∃ (B : ℝ) (Ξ : Set ((AdeleRing (𝓞 K) K)ˣ →* ℂˣ)), 0 ≤ B ∧ Ξ.Finite ∧
    (∀ ξ ∈ Ξ, IsUnitaryChar (𝓞 K) K ξ ∧ IsIdeleClassChar (𝓞 K) K ξ ∧
      Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξ z : ℂˣ) : ℂ)) ∧
    ∀ (μ ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 K) K μ) (_hν : IsUnitaryChar (𝓞 K) K ν)
      (_hμic : IsIdeleClassChar (𝓞 K) K μ) (_hνic : IsIdeleClassChar (𝓞 K) K ν)
      (_hμc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((μ z : ℂˣ) : ℂ))
      (_hνc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ν z : ℂˣ) : ℂ))
      (_hram : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S₀ →
        NumberField.TateGlobal.IsUnramifiedCharAt μ v ∧ NumberField.TateGlobal.IsUnramifiedCharAt ν v)
      (_hρ : ∃ r r' : Fin nρ, ∀ v ∈ S₀, ∀ u : (v.adicCompletion K)ˣ,
        (u : v.adicCompletion K) ∈ v.adicCompletionIntegers K →
        ((u⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) ∈ v.adicCompletionIntegers K →
          NumberField.TateGlobal.localChar μ v u = ρs r v u ∧ NumberField.TateGlobal.localChar ν v u = ρs r' v u)
      (τμ τν : InfinitePlace K → ℝ)
      (_hτμ : ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
        0 < (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).re →
        (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).im = 0 →
        ((NumberField.TateGlobal.archLocalChar μ v x : ℂˣ) : ℂ) =
          (((NumberField.TateGlobal.ideleNorm K (NumberField.TateGlobal.archUnitHom v x)) : ℝ) : ℂ) ^
            (((τμ v : ℝ) : ℂ) * Complex.I))
      (_hτν : ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
        0 < (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).re →
        (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).im = 0 →
        ((NumberField.TateGlobal.archLocalChar ν v x : ℂˣ) : ℂ) =
          (((NumberField.TateGlobal.ideleNorm K (NumberField.TateGlobal.archUnitHom v x)) : ℝ) : ℂ) ^
            (((τν v : ℝ) : ℂ) * Complex.I))
      (mμ mν : InfinitePlace K → ℤ)
      (_hmμ : ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
        ‖InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)‖ = 1 →
        ((NumberField.TateGlobal.archLocalChar μ v x : ℂˣ) : ℂ) =
          (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)) ^ (mμ v))
      (_hmν : ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
        ‖InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)‖ = 1 →
        ((NumberField.TateGlobal.archLocalChar ν v x : ℂˣ) : ℂ) =
          (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)) ^ (mν v))
      (_hreal : ∀ v : InfinitePlace K, v.IsReal → (mμ v = 0 ∨ mμ v = 1) ∧ (mν v = 0 ∨ mν v = 1))
      (_hdiff : ∀ v : InfinitePlace K, v.IsComplex → |mμ v - mν v| ≤ (n₀ : ℤ)),
    ∃ (η : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (τη : InfinitePlace K → ℝ) (mη : InfinitePlace K → ℤ),
      IsUnitaryChar (𝓞 K) K η ∧ IsIdeleClassChar (𝓞 K) K η ∧ Continuous η ∧
      (∀ v : HeightOneSpectrum (𝓞 K), NumberField.TateGlobal.IsUnramifiedCharAt η v) ∧
      (∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
        0 < (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).re →
        (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).im = 0 →
        ((NumberField.TateGlobal.archLocalChar η v x : ℂˣ) : ℂ) =
          (((NumberField.TateGlobal.ideleNorm K (NumberField.TateGlobal.archUnitHom v x)) : ℝ) : ℂ) ^
            (((τη v : ℝ) : ℂ) * Complex.I)) ∧
      (∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
        ‖InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)‖ = 1 →
        ((NumberField.TateGlobal.archLocalChar η v x : ℂˣ) : ℂ) =
          (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)) ^ (mη v)) ∧
      (∀ v : InfinitePlace K, v.IsReal → mη v = 0) ∧
      μ * ν * η ^ 2 ∈ Ξ ∧
      (∀ v : InfinitePlace K, |τμ v + τν v + 2 * τη v| ≤ B) ∧
      (∀ v : InfinitePlace K, (|mμ v + mη v| : ℝ) ≤ B ∧ (|mν v + mη v| : ℝ) ≤ B) ∧
      (∀ t : ℝ, 1 + ∑ v : InfinitePlace K,
          (|t + (τμ v + τη v)| + |t - (τν v + τη v)| + (|mμ v + mη v| : ℝ) + (|mν v + mη v| : ℝ)) ≤
        B * (1 + ∑ v : InfinitePlace K, |2 * t + (τμ v - τν v)|)) := by sorry
