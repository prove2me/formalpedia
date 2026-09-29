-- Prove2me | Theorems.Thm_ModularCurve_exists_isDiamondPullbackModL_of_isAlgClosed
-- name    : ModularCurve.exists_isDiamondPullbackModL_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.903374+00:00
-- url     : https://prove2.me/theorems/d0045110-d027-5b2c-b80b-fc79e7350d81
-- title:
--   Existence of a diamond pull-back action for arbitrary H
-- statement:
--   Let $K$ be an algebraically closed field, let $M$ be a positive integer whose image in $K$ is nonzero, and let $H$ be a subgroup of $(\mathbb{Z}/M)^{\times}$. Write $\Gamma_H(M) =$ [`CohCarrier.GammaH M H`](def/CohCarrier_Level.html#L133) for the subgroup of $\mathrm{SL}_2(\mathbb{Z})$ obtained as the image in $\mathrm{SL}_2(\mathbb{Z})$ of the set of $\gamma \in \Gamma_0(M)$ whose lower-right entry, viewed as a unit of $\mathbb{Z}/M$, lies in $H$, and write $F =$ [`ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H)`](def/ModularCurve_X1.html#L101) for the intermediate field of $K((q))$ generated over $K$ by all quotients $\bar{p}_f/\bar{p}_g$, where $f,g$ are modular forms of some common weight $k$ for $\Gamma_H(M)$ (as a subgroup of $\mathrm{GL}_2(\mathbb{R})$), $p_f,p_g$ are integral power series whose images in $\mathbb{C}[[q]]$ are the $q$-expansions of $f$ and $g$, the bar denotes reduction of coefficients to $K$ and $\bar{p}_g \neq 0$. The assertion is that there exists a group homomorphism $\rho\colon \Gamma_0(M) \to \mathrm{Aut}_K(F)$ satisfying [`ModularCurve.IsDiamondPullbackModL`](def/ModularCurve_XHDiamondModL.html#L12): for every $\gamma \in \Gamma_0(M)$, every weight $k$, all modular forms $f,g,f_1,g_1$ of weight $k$ for $\Gamma_H(M)$ with integral $q$-expansion power series $p_f,p_g,p_{f_1},p_{g_1}$, such that $f_1 = f\mid_k\gamma$ and $g_1 = g\mid_k\gamma$ as functions on the upper half plane and $\bar{p}_g \neq 0$, and every $x \in F$ whose underlying Laurent series is $\bar{p}_{f_1}/\bar{p}_{g_1}$, the Laurent series underlying $\rho(\gamma)(x)$ is $\bar{p}_f/\bar{p}_g$.
--
--   This is the existence of the reduced diamond action of $\Gamma_0(M)$ on the $q$-expansion model over $K$ of the modular curve $X_H(M)$, in the form of a pull-back formula on ratios of reduced integral $q$-expansions. It is the hypothesis under which the diamond operators on $X_H(M)$ and on its differentials over $K$ are defined by their intended values, and it is used in the analysis of places, Frobenius and differentials in the mod-$\ell$ models of these curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_isDiamondPullbackModL_of_isAlgClosed.lean

import Mathlib
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_XHDiamondModL

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.exists_isDiamondPullbackModL_of_isAlgClosed
    (K : Type*) [Field K] [IsAlgClosed K] (M : ℕ) [NeZero M] (hM : (M : K) ≠ 0)
    (H : Subgroup (ZMod M)ˣ) :
    ∃ ρ : CongruenceSubgroup.Gamma0 M →*
        (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H) ≃ₐ[K]
          ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H)),
      ModularCurve.IsDiamondPullbackModL K M H ρ := by sorry
