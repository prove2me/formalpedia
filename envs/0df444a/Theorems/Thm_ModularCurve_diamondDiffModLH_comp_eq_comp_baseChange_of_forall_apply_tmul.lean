-- Prove2me | Theorems.Thm_ModularCurve_diamondDiffModLH_comp_eq_comp_baseChange_of_forall_apply_tmul
-- name    : ModularCurve.diamondDiffModLH_comp_eq_comp_baseChange_of_forall_apply_tmul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.889759+00:00
-- url     : https://prove2.me/theorems/0ed5e24b-6546-51fe-9920-1fed2f3747ef
-- title:
--   Base change of diamond operators on differentials of X_{H'}(M/p)
-- statement:
--   Fix a prime $p$, a nonzero natural number $M$ with $p \mid M$ and $p^2 \nmid M$, a subgroup $H \le (\mathbb{Z}/M)^\times$, and a set $S \subseteq \mathbb{N}$ that enters no other hypothesis and not the conclusion. Put $N = M/p$ and let $H' =$ `infSubgroup p M H hpM` be the image of $H$ under the reduction map $(\mathbb{Z}/M)^\times \to (\mathbb{Z}/N)^\times$; write $\Gamma_{H'} \le \mathrm{SL}_2(\mathbb{Z})$ for the image in $\mathrm{SL}_2(\mathbb{Z})$ of the preimage of $H'$ under $\Gamma_0(N) \to (\mathbb{Z}/N)^\times$, and $F_L =$ `qExpFunctionFieldC L (CohCarrier.GammaH N H')` for the subfield of $L((q))$ generated over $L$ by the quotients $\mathrm{intSeriesC}\,L\,p_f / \mathrm{intSeriesC}\,L\,p_g$ attached to integral $q$-expansions $p_f, p_g \in \mathbb{Z}[[q]]$ of modular forms of some weight for $\Gamma_{H'}$, with nonzero denominator. Let $k$ be an algebraically closed field of characteristic $p$ and $K$ an algebraically closed extension field of $k$. Let $\Phi : K \otimes_k \Omega[F_k / k] \to \Omega[F_K / K]$ be an injective $K$-linear map such that $\Phi(c \otimes (f \cdot \mathrm{d}g)) = c\,(f' \cdot \mathrm{d}g')$ whenever $c \in K$, $f, g \in F_k$, and $f', g' \in F_K$ have Laurent series obtained from those of $f, g$ by applying $k \to K$ coefficientwise. Assume further that over $k$ and over $K$ there exists a monoid homomorphism $\rho$ from $\Gamma_0(N)$ to the group of $k$- resp. $K$-algebra automorphisms of the corresponding function field satisfying `IsDiamondPullbackModL`, i.e. $\rho(\gamma)$ sends any element whose Laurent series is $\mathrm{intSeriesC}\,p_{f_1} / \mathrm{intSeriesC}\,p_{g_1}$ to $\mathrm{intSeriesC}\,p_f / \mathrm{intSeriesC}\,p_g$ whenever $f_1 = f\mid_w\gamma$ and $g_1 = g\mid_w\gamma$ for modular forms of weight $w$ for $\Gamma_{H'}$ with these integral $q$-expansions and $\mathrm{intSeriesC}\,p_g \ne 0$. Finally let $N \ne 0$ and $d \in (\mathbb{Z}/N)^\times$. Then the diamond operator on differentials over $K$, namely pull-back along the chosen automorphism attached to a lift of $d^{-1}$ to $\Gamma_0(N)$, composed with $\Phi$, equals $\Phi$ composed with the base change to $K$ of the corresponding operator over $k$.
--
--   This is the diamond-operator case of the assertion that the comparison map $\Phi$ between the base-changed differentials over $k$ and the differentials over the larger algebraically closed field $K$ is equivariant for the operators on $\Omega$ of the modular curve of level $M/p$ with character group $H'$. It is used in the corresponding statement for the general operators built from diamonds, [`ModularCurve.genDiffModL_comp_eq_comp_baseChange_of_forall_apply_tmul`](thm.html#ModularCurve.genDiffModL_comp_eq_comp_baseChange_of_forall_apply_tmul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_diamondDiffModLH_comp_eq_comp_baseChange_of_forall_apply_tmul.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct
open ModularCurve AlgebraicCurve KaehlerDifferential

theorem ModularCurve.diamondDiffModLH_comp_eq_comp_baseChange_of_forall_apply_tmul
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
    (hρk : ∃ ρ : CongruenceSubgroup.Gamma0 (M / p) →*
        (↥(qExpFunctionFieldC k (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM))) ≃ₐ[k] ↥(qExpFunctionFieldC k (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)))),
      IsDiamondPullbackModL k (M / p) (infSubgroup p M H hpM) ρ)
    (hρK : ∃ ρ : CongruenceSubgroup.Gamma0 (M / p) →*
        (↥(qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM))) ≃ₐ[K] ↥(qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)))),
      IsDiamondPullbackModL K (M / p) (infSubgroup p M H hpM) ρ)
    (hN0 : NeZero (M / p)) (d : (ZMod (M / p))ˣ) :
    (diamondDiffModLH K (M / p) (infSubgroup p M H hpM) d) ∘ₗ Φ =
      Φ ∘ₗ (diamondDiffModLH k (M / p) (infSubgroup p M H hpM) d).baseChange K := by sorry
