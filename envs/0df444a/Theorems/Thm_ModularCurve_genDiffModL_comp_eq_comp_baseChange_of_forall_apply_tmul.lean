-- Prove2me | Theorems.Thm_ModularCurve_genDiffModL_comp_eq_comp_baseChange_of_forall_apply_tmul
-- name    : ModularCurve.genDiffModL_comp_eq_comp_baseChange_of_forall_apply_tmul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.414366+00:00
-- url     : https://prove2.me/theorems/ee6693e4-8f9e-50ca-ac4c-419b0fb730b2
-- title:
--   Hecke generators on differentials commute with base change k→ K
-- statement:
--   Fix a prime $p$ and a natural number $M \neq 0$ with $p \mid M$ and $p^2 \nmid M$, a subgroup $H \le (\mathbb{Z}/M)^{\times}$ and a set $S$ of natural numbers. Write $H'$ for `infSubgroup p M H hpM`, the image of $H$ under the reduction map $(\mathbb{Z}/M)^{\times} \to (\mathbb{Z}/(M/p))^{\times}$, and $\Gamma' =$ [`CohCarrier.GammaH (M/p) H'`](def/CohCarrier_Level.html#L133), the image in $\mathrm{SL}_2(\mathbb{Z})$ of the preimage of $H'$ under the determinant-type character $\Gamma_0(M/p) \to (\mathbb{Z}/(M/p))^{\times}$. For a field $L$ let $F_L =$ `qExpFunctionFieldC L Γ'` be the subfield of $L((q))$ generated over $L$ by the quotients $p_f/p_g$ of integral $q$-expansions of two modular forms of the same weight for $\Gamma'$ (with $p_g \neq 0$ in $L((q))$). Let $k$ be an algebraically closed field of characteristic $p$ and $K$ an algebraically closed field that is a $k$-algebra. Given are: a $K$-linear map $\Phi : K \otimes_k \Omega_{F_k/k} \to \Omega_{F_K/K}$; injectivity of $\Phi$; the hypothesis that $\Phi(c \otimes f\,\mathrm{d}g) = c\,(f'\,\mathrm{d}g')$ whenever $f', g' \in F_K$ have Laurent series obtained from those of $f, g \in F_k$ by applying $\mathrm{algebraMap}\ k\ K$ coefficientwise; the existence over $k$ and over $K$ of a linear endomorphism $C$ of $\Omega_{F/F\text{-base}}$ satisfying `IsFrobPushDiff`, i.e. the $q$-expansion of $C\omega$ is the $p$-decimation $a_n \mapsto a_{pn}$ of that of $\omega$; and the existence over $k$ and over $K$ of a homomorphism $\rho$ from $\Gamma_0(M/p)$ to the group of base-field algebra automorphisms of $F$ satisfying `IsDiamondPullbackModL`, i.e. $\rho(\gamma)$ sends any element whose Laurent series is $p_{f_1}/p_{g_1}$ to the one with series $p_f/p_g$ whenever $f_1 = f|_k\gamma$ and $g_1 = g|_k\gamma$ as functions on the upper half-plane, for forms with integral $q$-expansions and $p_g \neq 0$. Then for every generator $g$ of [`CohCarrier.Gen M S`](def/CohCarrier_Inst.html#L13) — a symbol $T_\ell$ for a prime $\ell \notin S$ with $\ell \nmid M$, a symbol $U_q$ for a prime $q \mid M$, or a diamond symbol $\langle d \rangle$ for $d \in (\mathbb{Z}/M)^{\times}$ — the operator `genDiffModL K p M H hpM S g` on $\Omega_{F_K/K}$ composed after $\Phi$ equals $\Phi$ composed after the base change to $K$ of `genDiffModL k p M H hpM S g`.
--
--   The operators `genDiffModL` realise the generators of the level-$M$ Hecke algebra on differentials of the component through $\infty$ of the special fibre at $p$ of the modular curve of level $\Gamma_{H'}(M/p)$: Hecke operators $T_\ell$ and $U_q$, the Cartier-type Frobenius push-forward in the case $q = p$, and the reduced diamond operators. The result says that this whole family is compatible with the embedding $K \otimes_k \Omega_{F_k/k} \hookrightarrow \Omega_{F_K/K}$ coming from extension of the algebraically closed base field, and it is used in the construction of Hecke-equivariant maps out of the supersingular-polar differentials and of the dual of the multiplicative part of the Tate module in the ordinary case.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_genDiffModL_comp_eq_comp_baseChange_of_forall_apply_tmul.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct
open ModularCurve AlgebraicCurve KaehlerDifferential

theorem ModularCurve.genDiffModL_comp_eq_comp_baseChange_of_forall_apply_tmul
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
    (hCk : ∃ C : Ω[↥(qExpFunctionFieldC k (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)))⁄k] →ₗ[k] Ω[↥(qExpFunctionFieldC k (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)))⁄k],
      haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩; IsFrobPushDiff k (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)) p C)
    (hCK : ∃ C : Ω[↥(qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)))⁄K] →ₗ[K] Ω[↥(qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)))⁄K],
      haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩; IsFrobPushDiff K (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)) p C)
    (hρk : ∃ ρ : CongruenceSubgroup.Gamma0 (M / p) →*
        (↥(qExpFunctionFieldC k (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM))) ≃ₐ[k] ↥(qExpFunctionFieldC k (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)))),
      IsDiamondPullbackModL k (M / p) (infSubgroup p M H hpM) ρ)
    (hρK : ∃ ρ : CongruenceSubgroup.Gamma0 (M / p) →*
        (↥(qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM))) ≃ₐ[K] ↥(qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)))),
      IsDiamondPullbackModL K (M / p) (infSubgroup p M H hpM) ρ)
    (g : CohCarrier.Gen M S) :
    (genDiffModL K p M H hpM S g) ∘ₗ Φ = Φ ∘ₗ (genDiffModL k p M H hpM S g).baseChange K := by sorry
