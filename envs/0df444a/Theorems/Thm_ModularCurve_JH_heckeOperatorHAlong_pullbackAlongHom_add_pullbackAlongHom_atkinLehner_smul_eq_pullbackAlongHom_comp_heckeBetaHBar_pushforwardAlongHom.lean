-- Prove2me | Theorems.Thm_ModularCurve_JH_heckeOperatorHAlong_pullbackAlongHom_add_pullbackAlongHom_atkinLehner_smul_eq_pullbackAlongHom_comp_heckeBetaHBar_pushforwardAlongHom
-- name    : ModularCurve.JH.heckeOperatorHAlong_pullbackAlongHom_add_pullbackAlongHom_atkinLehner_smul_eq_pullbackAlongHom_comp_heckeBetaHBar_pushforwardAlongHom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.860483+00:00
-- url     : https://prove2.me/theorems/2e314121-842b-5101-973a-3216a7ccc760
-- title:
--   Atkin–Lehner relation for Uₚ on Pic⁰ of modular curves
-- statement:
--   Fix $N\ge 1$, a prime $p$ with $p\nmid N$, and $M=Np$, together with subgroups $H'\le(\mathbb Z/N)^\times$ and $H\le(\mathbb Z/M)^\times$ such that $\Gamma_H(M)\le\Gamma_{H'}(N)$ as subgroups of $SL(2,\mathbb Z)$, and a unit $\bar p\in(\mathbb Z/N)^\times$ reducing to $p$. Write $F_0=\overline{\mathbb Q}\cdot F(\Gamma_{H'}(N))$, $F_1=\overline{\mathbb Q}\cdot F(\Gamma_{H'}(N)\cap\Gamma_0(Np))$ and $F_2=\overline{\mathbb Q}\cdot F(\Gamma_H(M))$ for the base-changed $q$-expansion function fields, with $\alpha\colon F_0\to F_1$ the inclusion `heckeAlphaHBar` and $\beta\colon F_0\to F_1$ the map `heckeBetaHBar`, which by the hypothesis `HeckeBetaHDefined` $N$ $H'$ $p$ is induced by $q\mapsto q^p$ on Laurent series. Assume: the data `HeckeInputsHAlong` at level $M$, $H$ and $p$ making the Hecke operator `heckeOperatorHAlong` equal to the $(\beta_M,\alpha_M)$-correspondence on $\operatorname{Pic}^0(F_2)$; an $\overline{\mathbb Q}$-algebra map $\iota\colon F_1\to F_2$ acting as the identity on underlying Laurent series; integrality of $\alpha$, finiteness along $\alpha$ and the push-forward norm formula for $\alpha$; existence of principal divisors for $F_1$ and $F_2$; integrality and the fundamental identity along $\iota$ and along $\beta$ followed by $\iota$; and an $\overline{\mathbb Q}$-automorphism $W$ of $F_1$ with $W\circ\beta=\alpha$ and $W\circ\alpha=\beta\circ\langle\bar p\rangle^{-1}$, where $\langle\bar p\rangle$ is `diamondAutHBar` $N$ $H'$ $\bar p$. Then for every $x\in\operatorname{Pic}^0(F_1)$ one has $U_p(\iota^*x)+\iota^*(W^{-1}\cdot x)=(\iota\circ\beta)^*(\alpha_*x)$, the action of $W^{-1}$ being through `SemilinearAut.ofAlgAut`.
--
--   This is the Atkin–Lehner style identity relating the Hecke operator $U_p$ at the prime $p$ dividing the level $M=Np$, acting on $\operatorname{Pic}^0$ of $X_H(M)$, to the two degeneracy maps from the level-$N$ curve and the Atkin–Lehner involution of the roof $X_{H'}(N)\cap X_0(Np)$. It is used in the analysis of the Jacobian $J_H(Np)$ at $p$, being cited in the proof of [`ModularCurve.JHNeronObjectAtP.genOpH_U_add_smul_eq_pull_degPts_of_roof`](thm.html#ModularCurve.JHNeronObjectAtP.genOpH_U_add_smul_eq_pull_degPts_of_roof).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JH_heckeOperatorHAlong_pullbackAlongHom_add_pullbackAlongHom_atkinLehner_smul_eq_pullbackAlongHom_comp_heckeBetaHBar_pushforwardAlongHom.lean

import Mathlib
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_ModularCurve_ShimuraKernel
import Definitions.Def_Isogeny_ConditionalCurrency

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.JH.heckeOperatorHAlong_pullbackAlongHom_add_pullbackAlongHom_atkinLehner_smul_eq_pullbackAlongHom_comp_heckeBetaHBar_pushforwardAlongHom
    (N p : ℕ) [NeZero N] [Fact p.Prime] (hpN : ¬ p ∣ N) (M : ℕ) [NeZero M] (hM : M = N * p)
    (H' : Subgroup (ZMod N)ˣ) (H : Subgroup (ZMod M)ˣ)
    (hle : CohCarrier.GammaH M H ≤ CohCarrier.GammaH N H')
    (pbar : (ZMod N)ˣ) (hpbar : (pbar : ZMod N) = p)
    (hin : ModularCurve.HeckeInputsHAlong (AlgebraicClosure ℚ) M H p)
    (hβN : ModularCurve.HeckeBetaHDefined N H' p)
    (ι : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
            (ModularCurve.xHTopFunctionFieldC ℚ N H' (N * p))) →ₐ[AlgebraicClosure ℚ]
        ↥(ModularCurve.xHFunctionFieldBar M H))
    (hιcoe : ∀ u : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
            (ModularCurve.xHTopFunctionFieldC ℚ N H' (N * p))),
      ((ι u : ↥(ModularCurve.xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
        (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hα : ModularCurve.HeckeAlphaHBarIntegral (AlgebraicClosure ℚ) N H' p)
    (hfinα : AlgebraicCurve.FiniteAlong (AlgebraicClosure ℚ)
      (ModularCurve.heckeAlphaHBar (AlgebraicClosure ℚ) N H' p))
    (hNα : AlgebraicCurve.NormFormulaAlong (AlgebraicClosure ℚ)
      (ModularCurve.heckeAlphaHBar (AlgebraicClosure ℚ) N H' p) hfinα)
    [AlgebraicCurve.HasPrincipalDivisors (AlgebraicClosure ℚ)
      ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
          (ModularCurve.xHTopFunctionFieldC ℚ N H' (N * p)))]
    [AlgebraicCurve.HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H)]
    (hι : ι.toRingHom.IsIntegral)
    (hFIι : AlgebraicCurve.FundamentalIdentityAlong (AlgebraicClosure ℚ) ι hι)
    (hιβ : (ι.comp (ModularCurve.heckeBetaHBar (AlgebraicClosure ℚ) N H' p)).toRingHom.IsIntegral)
    (hFIιβ : AlgebraicCurve.FundamentalIdentityAlong (AlgebraicClosure ℚ)
      (ι.comp (ModularCurve.heckeBetaHBar (AlgebraicClosure ℚ) N H' p)) hιβ)
    (W : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
            (ModularCurve.xHTopFunctionFieldC ℚ N H' (N * p))) ≃ₐ[AlgebraicClosure ℚ]
        ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
            (ModularCurve.xHTopFunctionFieldC ℚ N H' (N * p))))
    (hWβ : ∀ x : ↥(ModularCurve.xHFunctionFieldBar N H'),
        W (ModularCurve.heckeBetaHBar (AlgebraicClosure ℚ) N H' p x) =
          ModularCurve.heckeAlphaHBar (AlgebraicClosure ℚ) N H' p x)
    (hWα : ∀ x : ↥(ModularCurve.xHFunctionFieldBar N H'),
        W (ModularCurve.heckeAlphaHBar (AlgebraicClosure ℚ) N H' p x) =
          ModularCurve.heckeBetaHBar (AlgebraicClosure ℚ) N H' p
            ((ModularCurve.diamondAutHBar N H' pbar).symm x))
    (x : AlgebraicCurve.Pic0 (AlgebraicClosure ℚ)
      ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
          (ModularCurve.xHTopFunctionFieldC ℚ N H' (N * p)))) :
    ModularCurve.heckeOperatorHAlong (AlgebraicClosure ℚ) M H p
        (AlgebraicCurve.Pic0.pullbackAlongHom ι hι hFIι x) +
      AlgebraicCurve.Pic0.pullbackAlongHom ι hι hFIι
        (AlgebraicCurve.SemilinearAut.ofAlgAut W.symm • x) =
      AlgebraicCurve.Pic0.pullbackAlongHom
          (ι.comp (ModularCurve.heckeBetaHBar (AlgebraicClosure ℚ) N H' p)) hιβ hFIιβ
        (AlgebraicCurve.Pic0.pushforwardAlongHom
          (ModularCurve.heckeAlphaHBar (AlgebraicClosure ℚ) N H' p) hα hfinα hNα x) := by sorry
