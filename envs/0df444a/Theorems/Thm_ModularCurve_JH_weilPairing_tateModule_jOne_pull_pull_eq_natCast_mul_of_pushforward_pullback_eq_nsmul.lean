-- Prove2me | Theorems.Thm_ModularCurve_JH_weilPairing_tateModule_jOne_pull_pull_eq_natCast_mul_of_pushforward_pullback_eq_nsmul
-- name    : ModularCurve.JH.weilPairing_tateModule_jOne_pull_pull_eq_natCast_mul_of_pushforward_pullback_eq_nsmul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.860483+00:00
-- url     : https://prove2.me/theorems/a9c20e50-3275-54ab-bfcf-ca49b9b92c16
-- title:
--   Projection formula for the p-adic Weil pairing along X₁(M)→ X_H(M)
-- statement:
--   Fix $M\ge 1$, a subgroup $H\le(\mathbb Z/M)^\times$ and a prime $p$, and assume that every nonzero element of the two function fields $\overline{\mathbb Q}\cdot F(\Gamma_H(M))$ and $\overline{\mathbb Q}\cdot F(\Gamma_1(M))$ (realised as `xHFunctionFieldBar M H` and `x1FunctionFieldBar M`, intermediate fields of the Laurent series over $\overline{\mathbb Q}$) has an associated divisor of degree $0$ recording its orders at all places. Let $\zeta_n$ be, for each $n$, a primitive $p^n$-th root of unity in $\overline{\mathbb Q}$. Write $J_H=J_H(M)$ and $J_1=J_1(M)$ for the degree-zero divisor class groups of these fields, and $T_p(\cdot)$ for the Tate module of sequences $(x_n)$ with $p^nx_n=0$ and $px_{n+1}=x_n$. Let $e_H$ and $e_1$ be $\mathbb Z_p$-bilinear forms $T_pJ_H\times T_pJ_H\to\mathbb Z_p$, resp. $T_pJ_1\times T_pJ_1\to\mathbb Z_p$, each assumed to compute every divisorial Weil pairing data $W$ of order $p^n$ on the corresponding field in the sense that $W.\mathrm{pair}(a',b')=\zeta_n^{\,(e(a,b)).\mathrm{appr}\,n}$ whenever $a',b'$ are $p^n$-torsion classes equal to the $n$-th components of $a,b$. Let $\iota$ be a $\overline{\mathbb Q}$-algebra map from the $X_H$-field to the $X_1$-field that is the identity on underlying Laurent series. Let $\mathrm{pull}:J_H\to J_1$ and $\mathrm{push}:J_1\to J_H$ be additive maps which agree with the Picard pullback along $\iota$ (for any integrality witness and any fundamental-identity witness) and with the Picard pushforward along $\iota$ (for any integrality, finiteness and norm-formula witnesses) respectively, and let $c\in\mathbb N$ satisfy $\mathrm{push}(\mathrm{pull}\,x)=c\cdot x$ for all $x\in J_H$. Let $\mathrm{tpull}:T_pJ_H\to T_pJ_1$ be a $\mathbb Z_p$-linear map acting levelwise by $\mathrm{pull}$. Then for all $a,b\in T_pJ_H$ one has $e_1(\mathrm{tpull}\,a,\mathrm{tpull}\,b)=c\,e_H(a,b)$.
--
--   This is the projection formula, or functoriality under a finite covering, for the $p$-adic Weil pairing: pulling back along the covering $X_1(M)\to X_H(M)$ multiplies the pairing on Tate modules by the degree $c$ of the covering, the identity $e_1(\pi^*x,y)=e_H(x,\pi_*y)$ at each finite level $p^n$ being combined with $\pi_*\pi^*=c$. It is used in the study of the image of the degeneracy and inertia-augmentation maps on the diamond-fixed part of $T_pJ_1(M)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JH_weilPairing_tateModule_jOne_pull_pull_eq_natCast_mul_of_pushforward_pullback_eq_nsmul.lean

import Mathlib
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_ShimuraKernel
import Definitions.Def_Isogeny_ConditionalCurrency
import Definitions.Def_AlgebraicCurve_FunctionFieldWeilPairingDivisorial
import Definitions.Def_EllipticCurve_TateModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve
open ModularCurve

theorem ModularCurve.JH.weilPairing_tateModule_jOne_pull_pull_eq_natCast_mul_of_pushforward_pullback_eq_nsmul
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (p : ℕ) [Fact p.Prime]
    [AlgebraicCurve.HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar M)]
    [AlgebraicCurve.HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H)]

    (ζ : ℕ → AlgebraicClosure ℚ) (hζ : ∀ n : ℕ, IsPrimitiveRoot (ζ n) (p ^ n))

    (eH : TateModule p (ModularCurve.JH M H) →ₗ[ℤ_[p]] TateModule p (ModularCurve.JH M H) →ₗ[ℤ_[p]] ℤ_[p])
    (heH : ∀ (n : ℕ)
        (W : AlgebraicCurve.DivisorialWeilPairingData (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H) (p ^ n))
        (a b : TateModule p (ModularCurve.JH M H))
        (a' b' : AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H) (p ^ n)),
        (a' : ModularCurve.JH M H) = (a : ℕ → ModularCurve.JH M H) n →
        (b' : ModularCurve.JH M H) = (b : ℕ → ModularCurve.JH M H) n →
        W.pair a' b' = ζ n ^ ((eH a b).appr n))

    (e₁ : TateModule p (ModularCurve.JOne M) →ₗ[ℤ_[p]] TateModule p (ModularCurve.JOne M) →ₗ[ℤ_[p]] ℤ_[p])
    (he₁ : ∀ (n : ℕ)
        (W : AlgebraicCurve.DivisorialWeilPairingData (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar M) (p ^ n))
        (a b : TateModule p (ModularCurve.JOne M))
        (a' b' : AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar M) (p ^ n)),
        (a' : ModularCurve.JOne M) = (a : ℕ → ModularCurve.JOne M) n →
        (b' : ModularCurve.JOne M) = (b : ℕ → ModularCurve.JOne M) n →
        W.pair a' b' = ζ n ^ ((e₁ a b).appr n))

    (ι : ↥(ModularCurve.xHFunctionFieldBar M H) →ₐ[AlgebraicClosure ℚ] ↥(ModularCurve.x1FunctionFieldBar M))
    (hι : ∀ x : ↥(ModularCurve.xHFunctionFieldBar M H),
      ((ι x : ↥(ModularCurve.x1FunctionFieldBar M)) : LaurentSeries (AlgebraicClosure ℚ)) =
        (x : LaurentSeries (AlgebraicClosure ℚ)))

    (pull : ModularCurve.JH M H →+ ModularCurve.JOne M) (push : ModularCurve.JOne M →+ ModularCurve.JH M H) (c : ℕ)
    (hpinPull : ∀ (hint : ι.toRingHom.IsIntegral)
        (hFI : AlgebraicCurve.FundamentalIdentityAlong (AlgebraicClosure ℚ) ι hint)
        (x : ModularCurve.JH M H),
      pull x = AlgebraicCurve.Pic0.pullbackAlongHom ι hint hFI x)
    (hpinPush : ∀ (hint : ι.toRingHom.IsIntegral)
        (hfin : AlgebraicCurve.FiniteAlong (AlgebraicClosure ℚ) ι)
        (hN : AlgebraicCurve.NormFormulaAlong (AlgebraicClosure ℚ) ι hfin)
        (y : ModularCurve.JOne M),
      push y = AlgebraicCurve.Pic0.pushforwardAlongHom ι hint hfin hN y)
    (hdeg : ∀ x : ModularCurve.JH M H, push (pull x) = c • x)

    (tpull : TateModule p (ModularCurve.JH M H) →ₗ[ℤ_[p]] TateModule p (ModularCurve.JOne M))
    (htpull : ∀ (a : TateModule p (ModularCurve.JH M H)) (n : ℕ),
      ((tpull a : TateModule p (ModularCurve.JOne M)) : ℕ → ModularCurve.JOne M) n =
        pull ((a : ℕ → ModularCurve.JH M H) n))
    (a b : TateModule p (ModularCurve.JH M H)) :
    e₁ (tpull a) (tpull b) = (c : ℤ_[p]) * eH a b := by sorry
