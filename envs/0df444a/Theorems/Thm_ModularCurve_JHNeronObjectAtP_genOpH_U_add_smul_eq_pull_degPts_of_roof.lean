-- Prove2me | Theorems.Thm_ModularCurve_JHNeronObjectAtP_genOpH_U_add_smul_eq_pull_degPts_of_roof
-- name    : ModularCurve.JHNeronObjectAtP.genOpH_U_add_smul_eq_pull_degPts_of_roof
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.315379+00:00
-- url     : https://prove2.me/theorems/7d0a29c6-3398-5a41-8a83-e40c53425846
-- title:
--   Uₚ plus Atkin–Lehner equals degeneracy pull-push on J_H(M)
-- statement:
--   Fix a prime $p$ and $M$ with $p \mid M$, $p \nmid M/p$ and $M = (M/p)\cdot p$, a subgroup $H \le (\mathbb{Z}/M)^\times$, and write $H' =$ `infSubgroup p M H hpM` for the image of $H$ in $(\mathbb{Z}/(M/p))^\times$ under `ZMod.unitsMap`. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ in its nonunits, with algebraically closed residue field of characteristic $p$, let $\Lambda$ be level data and $O$ a Néron object `JHNeronObjectAtP p M H hpM A hA Λ`, and let $S$ be a set of naturals; the two function fields $\overline{F}_H(M)$ and $\overline{F}_{H'}(M/p)$ (the $\overline{\mathbb{Q}}$-base changes `xHFunctionFieldBar`) are assumed to have principal divisors. Assume given: integral $\overline{\mathbb{Q}}$-algebra maps $\alpha_H,\beta_H : \overline{F}_{H'}(M/p) \to \overline{F}_H(M)$ acting on Laurent series as the identity, respectively as `qExpand` by $p$; maps $\alpha\mathrm{pull} : \mathrm{Fin}\,2 \to (J_{H'}(M/p) \to_+ J_H(M))$; the divisor-level pinnings that $O.\mathrm{degPts}\,0$ sends the class of a degree-zero divisor $D_v$ to the class of its push-forward along $\alpha_H$, and that $\alpha\mathrm{pull}\,1$ sends the class of $D_w$ to the class of its pull-back along $\beta_H$; the inclusion $\Gamma_H(M) \le \Gamma_{H'}(M/p)$; a unit $\bar p$ of $\mathbb{Z}/(M/p)$ reducing to $p$; the Hecke data `HeckeInputsHAlong` at level $M,H$ for $p$ and `HeckeBetaHDefined` at level $M/p,H'$ for $p$; an integral algebra map $\iota$ from the base change of `xHTopFunctionFieldC ℚ (M/p) H' ((M/p)*p)` (level $\Gamma_{H'}(M/p) \cap \Gamma_0((M/p)p)$) into $\overline{F}_H(M)$ that is the identity on Laurent series and satisfies the fundamental identity, as does $\iota$ precomposed with `heckeBetaHBar`, together with integrality, finiteness, norm-formula and principal-divisor hypotheses for `heckeAlphaHBar`; an automorphism $W$ of the roof field with $W \circ \beta = \alpha$ and $W \circ \alpha = \beta \circ \langle \bar p\rangle^{-1}$ (the inverse of `diamondAutHBar`); surjectivity of the induced map $\iota^*$ on $\mathrm{Pic}^0$; the divisor identity $\alpha_{H*}\iota^* =$ push-forward along `heckeAlphaHBar`; and an automorphism $\theta$ of $\overline{F}_H(M)$ whose semilinear action commutes with $\iota^*$ in the sense that $\theta \cdot \iota^*(x_1) = \iota^*(W^{-1} \cdot x_1)$ for all $x_1$. Then for every $x \in J_H(M)$, $$\mathrm{genOpH}\,M\,H\,S(U_p)(x) + \theta \cdot x = \alpha\mathrm{pull}\,1\,(O.\mathrm{degPts}\,0\,x),$$ where the left-hand operator is the Hecke operator `heckeOperatorHAlong` at $p$ attached to the generator `CohCarrier.Gen.U p`.
--
--   This is the Atkin–Lehner relation $U_p + W = \beta_H^* \circ \alpha_{H*}$ on $J_H(M)(\overline{\mathbb{Q}})$ for $p$ exactly dividing $M$, transcribed into the degeneracy maps $O.\mathrm{degPts}\,0$ and $\alpha\mathrm{pull}\,1$ carried by a Néron object of $J_H(M)$ at $p$. In this form it feeds the description of $U_p$ on the special fibre, and it is used by [`ModularCurve.JHNeronObjectAtP.genOpH_U_add_ofAlgAut_smul_eq_pull_degPts_of_coe_eq_qExpand`](thm.html#ModularCurve.JHNeronObjectAtP.genOpH_U_add_ofAlgAut_smul_eq_pull_degPts_of_coe_eq_qExpand).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHNeronObjectAtP_genOpH_U_add_smul_eq_pull_degPts_of_roof.lean

import Mathlib
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_Isogeny_ConditionalCurrency
import Definitions.Def_ModularCurve_ShimuraKernel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open AlgebraicCurve ModularCurve

theorem ModularCurve.JHNeronObjectAtP.genOpH_U_add_smul_eq_pull_degPts_of_roof
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) [NeZero (M / p)]
    (hpN : ¬ p ∣ M / p) (hM : M = M / p * p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (Λ : JHNeronObjectAtP.LevelData p M H hpM A) (O : JHNeronObjectAtP p M H hpM A hA Λ)
    (S : Set ℕ)
    [AlgebraicCurve.HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H)]
    [AlgebraicCurve.HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM))]

    (αH βH : ↥(ModularCurve.xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(ModularCurve.xHFunctionFieldBar M H))
    (hαint : αH.toRingHom.IsIntegral) (hβint : βH.toRingHom.IsIntegral)
    (hαq : ∀ u : ↥(ModularCurve.xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM)), ((αH u : ↥(ModularCurve.xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hβq : ∀ u : ↥(ModularCurve.xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM)), ((βH u : ↥(ModularCurve.xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
      qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))
    (αpull : Fin 2 → (JH (M / p) (ModularCurve.infSubgroup p M H hpM) →+ JH M H))

    (hdeg0 : ∀ (Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(ModularCurve.xHFunctionFieldBar M H)))
        (Dw : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(ModularCurve.xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM)))),
      (Dw : Divisor (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM))) = Divisor.pushforwardAlong αH hαint (Dv : Divisor (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H)) →
        O.degPts 0 (Pic0.mk Dv) = Pic0.mk Dw)
    (hpull1 : ∀ (Dw : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(ModularCurve.xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM))))
        (Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(ModularCurve.xHFunctionFieldBar M H))),
      (Dv : Divisor (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H)) = Divisor.pullbackAlong βH hβint (Dw : Divisor (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM))) →
        αpull 1 (Pic0.mk Dw) = Pic0.mk Dv)

    (hle : CohCarrier.GammaH M H ≤ CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))
    (pbar : (ZMod (M / p))ˣ) (hpbar : (pbar : ZMod (M / p)) = p)
    (hin : ModularCurve.HeckeInputsHAlong (AlgebraicClosure ℚ) M H p)
    (hβN : ModularCurve.HeckeBetaHDefined (M / p) (ModularCurve.infSubgroup p M H hpM) p)
    (ι : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
            (ModularCurve.xHTopFunctionFieldC ℚ (M / p) (ModularCurve.infSubgroup p M H hpM) (M / p * p))) →ₐ[AlgebraicClosure ℚ]
        ↥(ModularCurve.xHFunctionFieldBar M H))
    (hιcoe : ∀ u : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
            (ModularCurve.xHTopFunctionFieldC ℚ (M / p) (ModularCurve.infSubgroup p M H hpM) (M / p * p))),
      ((ι u : ↥(ModularCurve.xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
        (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hα : ModularCurve.HeckeAlphaHBarIntegral (AlgebraicClosure ℚ) (M / p) (ModularCurve.infSubgroup p M H hpM) p)
    (hfinα : AlgebraicCurve.FiniteAlong (AlgebraicClosure ℚ)
      (ModularCurve.heckeAlphaHBar (AlgebraicClosure ℚ) (M / p) (ModularCurve.infSubgroup p M H hpM) p))
    (hNα : AlgebraicCurve.NormFormulaAlong (AlgebraicClosure ℚ)
      (ModularCurve.heckeAlphaHBar (AlgebraicClosure ℚ) (M / p) (ModularCurve.infSubgroup p M H hpM) p) hfinα)
    [AlgebraicCurve.HasPrincipalDivisors (AlgebraicClosure ℚ)
      ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
          (ModularCurve.xHTopFunctionFieldC ℚ (M / p) (ModularCurve.infSubgroup p M H hpM) (M / p * p)))]
    [AlgebraicCurve.HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H)]
    (hι : ι.toRingHom.IsIntegral)
    (hFIι : AlgebraicCurve.FundamentalIdentityAlong (AlgebraicClosure ℚ) ι hι)
    (hιβ : (ι.comp (ModularCurve.heckeBetaHBar (AlgebraicClosure ℚ) (M / p) (ModularCurve.infSubgroup p M H hpM) p)).toRingHom.IsIntegral)
    (hFIιβ : AlgebraicCurve.FundamentalIdentityAlong (AlgebraicClosure ℚ)
      (ι.comp (ModularCurve.heckeBetaHBar (AlgebraicClosure ℚ) (M / p) (ModularCurve.infSubgroup p M H hpM) p)) hιβ)
    (W : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
            (ModularCurve.xHTopFunctionFieldC ℚ (M / p) (ModularCurve.infSubgroup p M H hpM) (M / p * p))) ≃ₐ[AlgebraicClosure ℚ]
        ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
            (ModularCurve.xHTopFunctionFieldC ℚ (M / p) (ModularCurve.infSubgroup p M H hpM) (M / p * p))))
    (hWβ : ∀ x : ↥(ModularCurve.xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM)),
        W (ModularCurve.heckeBetaHBar (AlgebraicClosure ℚ) (M / p) (ModularCurve.infSubgroup p M H hpM) p x) =
          ModularCurve.heckeAlphaHBar (AlgebraicClosure ℚ) (M / p) (ModularCurve.infSubgroup p M H hpM) p x)
    (hWα : ∀ x : ↥(ModularCurve.xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM)),
        W (ModularCurve.heckeAlphaHBar (AlgebraicClosure ℚ) (M / p) (ModularCurve.infSubgroup p M H hpM) p x) =
          ModularCurve.heckeBetaHBar (AlgebraicClosure ℚ) (M / p) (ModularCurve.infSubgroup p M H hpM) p
            ((ModularCurve.diamondAutHBar (M / p) (ModularCurve.infSubgroup p M H hpM) pbar).symm x))

    (hιsurj : Function.Surjective (Pic0.pullbackAlongHom ι hι hFIι))
    (hιdegα : ∀ D : Divisor (AlgebraicClosure ℚ)
        ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
          (ModularCurve.xHTopFunctionFieldC ℚ (M / p) (ModularCurve.infSubgroup p M H hpM) (M / p * p))),
      Divisor.pushforwardAlong αH hαint (Divisor.pullbackAlong ι hι D) =
        Divisor.pushforwardAlong (ModularCurve.heckeAlphaHBar (AlgebraicClosure ℚ) (M / p) (ModularCurve.infSubgroup p M H hpM) p) hα D)
    (θ : ↥(ModularCurve.xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(ModularCurve.xHFunctionFieldBar M H))
    (hθι : ∀ x₁ : Pic0 (AlgebraicClosure ℚ)
        ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
          (ModularCurve.xHTopFunctionFieldC ℚ (M / p) (ModularCurve.infSubgroup p M H hpM) (M / p * p))),
      SemilinearAut.ofAlgAut θ • Pic0.pullbackAlongHom ι hι hFIι x₁ =
        Pic0.pullbackAlongHom ι hι hFIι (SemilinearAut.ofAlgAut W.symm • x₁)) :
    ∀ x : JH M H,
      genOpH M H S (CohCarrier.Gen.U p Fact.out hpM) x + SemilinearAut.ofAlgAut θ • x = αpull 1 (O.degPts 0 x) := by sorry
