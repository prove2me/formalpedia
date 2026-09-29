-- Prove2me | Theorems.Thm_ModularCurve_heckeDiffModLH_comp_eq_comp_baseChange_of_forall_apply_tmul_of_prime
-- name    : ModularCurve.heckeDiffModLH_comp_eq_comp_baseChange_of_forall_apply_tmul_of_prime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.700479+00:00
-- url     : https://prove2.me/theorems/c9240fc8-57fb-5d5b-a867-6d8283932a5d
-- title:
--   Base change compatibility of Hecke operators on modular differentials
-- statement:
--   Fix a prime $p$ and a natural number $M$ with $p \mid M$ and $p^2 \nmid M$, a subgroup $H \le (\mathbb{Z}/M)^\times$, and a set $S \subseteq \mathbb{N}$ (which does not occur in the conclusion). Put $N = M/p$, assumed nonzero, and let $H'$ be `infSubgroup p M H hpM`, the image of $H$ in $(\mathbb{Z}/N)^\times$ under reduction along $N \mid M$; write $\Gamma_{H'}(N)$ for [`CohCarrier.GammaH N H'`](def/CohCarrier_Level.html#L133), the subgroup of $\mathrm{SL}(2,\mathbb{Z})$ obtained by pulling $H'$ back along the homomorphism $\Gamma_0(N) \to (\mathbb{Z}/N)^\times$, $\gamma \mapsto d \bmod N$. Let $k$ be an algebraically closed field of characteristic $p$ and $K$ an algebraically closed field which is a $k$-algebra. For a field $L$, let $F_L =$ `qExpFunctionFieldC L` $\Gamma_{H'}(N)$ be the subfield of $\mathrm{LaurentSeries}(L)$ generated over $L$ by the quotients of $L$-Laurent series coming from integral $q$-expansions of pairs of modular forms for $\Gamma_{H'}(N)$. Let $\Phi : K \otimes_k \Omega_{F_k/k} \to \Omega_{F_K/K}$ be an injective $K$-linear map satisfying: for all $c \in K$, all $f, g \in F_k$ and all $f', g' \in F_K$ whose underlying Laurent series are the coefficientwise images of those of $f$ and $g$ under $k \to K$, one has $\Phi(c \otimes f\,\mathrm{d}g) = c\,(f'\,\mathrm{d}g')$. Finally let $\ell$ be a prime, nonzero as a natural number, with $\ell \ne 0$ in $K$. The conclusion is the identity of $K$-linear endomorphisms $$T_{\ell,K} \circ \Phi = \Phi \circ (\mathrm{id}_K \otimes T_{\ell,k}),$$ where for $L \in \{k, K\}$ the operator $T_{\ell,L} =$ `heckeDiffModLH L N H'` $\ell$ on $\Omega_{F_L/L}$ is the pullback of differentials along `heckeAlphaModLH` (the inclusion $F_L \hookrightarrow$ `qExpFunctionFieldC L` $(\Gamma_{H'}(N) \cap \Gamma_0(N\ell))$) followed by the trace along `heckeBetaModLH` (the second degeneracy map, whose definition branches on the predicate `HeckeBetaModLHDefined`, which always holds), and the right-hand side is the base change to $K$ of the $k$-linear operator $T_{\ell,k}$.
--
--   This is the compatibility of the Hecke correspondence $T_\ell$ (equivalently $U_\ell$ for $\ell$ dividing the level) on differentials of the modular curve $X_{H'}(M/p)$ with extension of the algebraically closed constant field, for primes $\ell$ invertible in $K$. It feeds into [`ModularCurve.genDiffModL_comp_eq_comp_baseChange_of_forall_apply_tmul`](thm.html#ModularCurve.genDiffModL_comp_eq_comp_baseChange_of_forall_apply_tmul), where the Hecke action on the mod-$p$ differential realisation is transported between base fields.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_heckeDiffModLH_comp_eq_comp_baseChange_of_forall_apply_tmul_of_prime.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct
open AlgebraicCurve KaehlerDifferential
open ModularCurve

theorem ModularCurve.heckeDiffModLH_comp_eq_comp_baseChange_of_forall_apply_tmul_of_prime
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (H : Subgroup (ZMod M)ˣ) (S : Set ℕ)
    (k : Type) [Field k] [IsAlgClosed k] [CharP k p]
    (K : Type*) [Field K] [IsAlgClosed K] [Algebra k K]
    (Φ : K ⊗[k] Ω[↥(qExpFunctionFieldC k (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)))⁄k] →ₗ[K]
        Ω[↥(qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)))⁄K])
    (hinj : Function.Injective Φ)
    (hΦ : (∀ (c : K) (f g : ↥(qExpFunctionFieldC k (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM))))
          (f' g' : ↥(qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)))),
          (f' : LaurentSeries K) = coeffMap (algebraMap k K) (f : LaurentSeries k) →
          (g' : LaurentSeries K) = coeffMap (algebraMap k K) (g : LaurentSeries k) →
          Φ (c ⊗ₜ[k] (f • D k ↥(qExpFunctionFieldC k (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM))) g)) =
            c • (f' • D K ↥(qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM))) g')))
    (hN0 : NeZero (M / p)) (ℓ : ℕ) [NeZero ℓ] (hℓ : ℓ.Prime) (hℓK : (ℓ : K) ≠ 0) :
    (heckeDiffModLH K (M / p) (infSubgroup p M H hpM) ℓ) ∘ₗ Φ =
      Φ ∘ₗ (heckeDiffModLH k (M / p) (infSubgroup p M H hpM) ℓ).baseChange K := by sorry
