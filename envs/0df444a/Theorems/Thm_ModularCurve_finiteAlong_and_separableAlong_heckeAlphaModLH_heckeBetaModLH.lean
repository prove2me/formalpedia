-- Prove2me | Theorems.Thm_ModularCurve_finiteAlong_and_separableAlong_heckeAlphaModLH_heckeBetaModLH
-- name    : ModularCurve.finiteAlong_and_separableAlong_heckeAlphaModLH_heckeBetaModLH
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.061738+00:00
-- url     : https://prove2.me/theorems/4250d0c2-0194-501e-8215-1bbac2b0d29d
-- title:
--   Finiteness and separability along the degeneracy maps α,β
-- statement:
--   Let $K$ be an algebraically closed field, $N$ a nonzero natural number, $H'$ a subgroup of $(\mathbb{Z}/N\mathbb{Z})^{\times}$, and $\ell$ a prime which is nonzero in $K$. Write $\Gamma_{H'} =$ [`CohCarrier.GammaH N H'`](def/CohCarrier_Level.html#L133) for the subgroup of $\mathrm{SL}_2(\mathbb{Z})$ obtained as the image under the inclusion of $\Gamma_0(N)$ of the preimage of $H'$ along the unit-character map `gamma0Units N`, and for a subgroup $\Gamma$ let $\bar F(\Gamma) =$ [`ModularCurve.qExpFunctionFieldC K Γ`](def/ModularCurve_X1.html#L101) be the intermediate field of $K((q))$ generated over $K$ by the set `intFormRatiosC K Γ`. Two $K$-algebra maps $\bar F(\Gamma_{H'}) \to \bar F(\Gamma_{H'} \cap \Gamma_0(N\ell))$ are in play: `heckeAlphaModLH`, the inclusion coming from the inclusion of the corresponding fields of $q$-expansions, and `heckeBetaModLH`, which is the substitution $y(q) \mapsto y(q^{\ell})$ given by `qExpand K ℓ` when that substitution carries $\bar F(\Gamma_{H'})$ into $\bar F(\Gamma_{H'} \cap \Gamma_0(N\ell))$, and is the inclusion otherwise. The assertion is the conjunction of four statements: with respect to the algebra structure induced on $\bar F(\Gamma_{H'} \cap \Gamma_0(N\ell))$ by each of the two maps, the larger field is a finite module over $\bar F(\Gamma_{H'})$, and the extension is separable; that is, `FiniteAlong` and `SeparableAlong` hold along $\alpha$ and along $\beta$.
--
--   This is Igusa's statement that, in characteristic prime to $\ell$, the two degeneracy maps of the Hecke correspondence $T_\ell$ (respectively $U_\ell$ when $\ell \mid N$) on the modular curve attached to $\Gamma_{H'}(N)$ are finite and separable. It is the hypothesis under which the trace of Kähler differentials along $\beta$ is defined and computes the expected value, and it is used in the determination of the $q$-expansion coefficients of the Hecke operator on differentials and in the construction of the algebra equivalences intertwining $\alpha$ and $\beta$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_finiteAlong_and_separableAlong_heckeAlphaModLH_heckeBetaModLH.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.finiteAlong_and_separableAlong_heckeAlphaModLH_heckeBetaModLH
    (K : Type*) [Field K] [IsAlgClosed K] (N : ℕ) [NeZero N] (H' : Subgroup (ZMod N)ˣ)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓK : (ℓ : K) ≠ 0) :
    AlgebraicCurve.FiniteAlong K (ModularCurve.heckeAlphaModLH K N H' ℓ) ∧
    AlgebraicCurve.FiniteAlong K (ModularCurve.heckeBetaModLH K N H' ℓ) ∧
    AlgebraicCurve.SeparableAlong K (ModularCurve.heckeAlphaModLH K N H' ℓ) ∧
    AlgebraicCurve.SeparableAlong K (ModularCurve.heckeBetaModLH K N H' ℓ) := by sorry
