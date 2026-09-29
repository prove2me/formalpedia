-- Prove2me | Theorems.Thm_ModularCurve_exists_algEquiv_qExpFunctionFieldC_heckeBetaModLH_eq_heckeAlphaModLH_and_eq_diamondActionModL_of_charP
-- name    : ModularCurve.exists_algEquiv_qExpFunctionFieldC_heckeBetaModLH_eq_heckeAlphaModLH_and_eq_diamondActionModL_of_charP
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.209688+00:00
-- url     : https://prove2.me/theorems/29743ed4-32ae-5400-9275-84288bd8e6c5
-- title:
--   Atkin–Lehner automorphism W in positive characteristic
-- statement:
--   Let $K$ be an algebraically closed field of characteristic $p$ for a prime $p$, let $N \ge 1$, let $H' \le (\mathbb Z/N)^\times$ and let $\ell$ be a prime with $\gcd(\ell,N)=1$, and assume that the images of $N$ and of $\ell$ in $K$ are nonzero. Write $\Gamma_{H'}(N) \le \mathrm{SL}_2(\mathbb Z)$ for the subgroup [`CohCarrier.GammaH N H'`](def/CohCarrier_Level.html#L133), the preimage in $\Gamma_0(N)$ of $H'$ under the reduction of the lower-right entry, and for a subgroup $\Gamma$ write $F(\Gamma) =$ [`ModularCurve.qExpFunctionFieldC K Γ`](def/ModularCurve_X1.html#L101) for the intermediate field of $K((q))$ (Laurent series over $K$) generated over $K$ by the quotients $\mathrm{intSeriesC}\,p_f/\mathrm{intSeriesC}\,p_g$ of reductions to $K$ of integral $q$-expansions $p_f,p_g \in \mathbb Z[[q]]$ of modular forms $f,g$ of a common weight $k$ on $\Gamma$, with $\mathrm{intSeriesC}\,p_g \ne 0$. Assume [`ModularCurve.HeckeBetaModLHDefined K N H' ℓ`](def/ModularCurve_XHDifferentialsModL.html#L143): substitution $q \mapsto q^{\ell}$ (the exponent-scaling ring homomorphism [`ModularCurve.qExpand K ℓ`](def/ModularCurve_X0.html#L25)) maps $F(\Gamma_{H'}(N))$ into $F(\Gamma_{H'}(N) \cap \Gamma_0(N\ell))$, so that `heckeBetaModLH`, denoted $\beta$, is this substitution map; let $\alpha$ = `heckeAlphaModLH` be the inclusion $F(\Gamma_{H'}(N)) \hookrightarrow F(\Gamma_{H'}(N) \cap \Gamma_0(N\ell))$ coming from $\Gamma_{H'}(N) \cap \Gamma_0(N\ell) \le \Gamma_{H'}(N)$. Assume further that there exists a homomorphism $\rho$ from $\Gamma_0(N)$ to the $K$-algebra automorphisms of $F(\Gamma_{H'}(N))$ satisfying [`ModularCurve.IsDiamondPullbackModL`](def/ModularCurve_XHDiamondModL.html#L12), i.e. compatible with weight-$k$ slash pull-back of ratios of integral $q$-expansions; then [`ModularCurve.diamondActionModL K N H'`](def/ModularCurve_XHDifferentialsModL.html#L203) is such a $\rho$. The conclusion is that there is a $K$-algebra automorphism $W$ of $F(\Gamma_{H'}(N) \cap \Gamma_0(N\ell))$ with $W(\beta x) = \alpha x$ and $W(\alpha x) = \beta\big(\rho(\gamma) x\big)$ for all $x \in F(\Gamma_{H'}(N))$, where $\gamma =$ [`CuspForm.gammaLift N (ZMod.unitOfCoprime ℓ hcop)⁻¹`](def/CuspForm_HeckeOperatorFormsGammaH.html#L36) is the chosen element of $\Gamma_0(N)$ whose lower-right entry reduces to $\ell^{-1} \bmod N$.
--
--   This is the Atkin–Lehner involution $w_\ell$, realised as pull-back of functions on the $q$-expansion function field of $X_{H'}(N) \cap X_0(N\ell)$ over an algebraically closed field of positive characteristic, together with the two relations relating the degeneracy maps $\alpha$ (inclusion) and $\beta$ ($q \mapsto q^{\ell}$) through the diamond operator $\langle \ell \rangle$. It is used in the comparison of Hecke correspondences with differentials in characteristic $p$, in particular by [`ModularCurve.coeff_diffQExp_heckeDiffModLH_of_not_dvd_of_charP`](thm.html#ModularCurve.coeff_diffQExp_heckeDiffModLH_of_not_dvd_of_charP) and by [`ModularCurve.twist_correspondence_heckeT_eq_genDiffModL_T_of_atkinLehnerPinAlong`](thm.html#ModularCurve.twist_correspondence_heckeT_eq_genDiffModL_T_of_atkinLehnerPinAlong).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_algEquiv_qExpFunctionFieldC_heckeBetaModLH_eq_heckeAlphaModLH_and_eq_diamondActionModL_of_charP.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.exists_algEquiv_qExpFunctionFieldC_heckeBetaModLH_eq_heckeAlphaModLH_and_eq_diamondActionModL_of_charP
    (K : Type*) [Field K] [IsAlgClosed K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (N : ℕ) [NeZero N] (H' : Subgroup (ZMod N)ˣ)
    (ℓ : ℕ) [Fact ℓ.Prime] (hcop : ℓ.Coprime N) (hNK : ((N : ℕ) : K) ≠ 0) (hℓK : ((ℓ : ℕ) : K) ≠ 0)
    (hβ : ModularCurve.HeckeBetaModLHDefined K N H' ℓ)
    (hdia : ∃ ρ : CongruenceSubgroup.Gamma0 N →*
        (↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H')) ≃ₐ[K] ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H'))),
      ModularCurve.IsDiamondPullbackModL K N H' ρ) :
    ∃ W : ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H' ⊓ CongruenceSubgroup.Gamma0 (N * ℓ))) ≃ₐ[K]
        ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H' ⊓ CongruenceSubgroup.Gamma0 (N * ℓ))),
      (∀ x : ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H')),
        W (ModularCurve.heckeBetaModLH K N H' ℓ x) = ModularCurve.heckeAlphaModLH K N H' ℓ x) ∧
      (∀ x : ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H')),
        W (ModularCurve.heckeAlphaModLH K N H' ℓ x) =
          ModularCurve.heckeBetaModLH K N H' ℓ
            (ModularCurve.diamondActionModL K N H'
              (CuspForm.gammaLift N (ZMod.unitOfCoprime ℓ hcop)⁻¹) x)) := by sorry
