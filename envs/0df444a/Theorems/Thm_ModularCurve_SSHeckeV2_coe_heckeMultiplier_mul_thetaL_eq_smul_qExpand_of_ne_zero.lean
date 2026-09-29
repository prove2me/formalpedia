-- Prove2me | Theorems.Thm_ModularCurve_SSHeckeV2_coe_heckeMultiplier_mul_thetaL_eq_smul_qExpand_of_ne_zero
-- name    : ModularCurve.SSHeckeV2.coe_heckeMultiplier_mul_thetaL_eq_smul_qExpand_of_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.379182+00:00
-- url     : https://prove2.me/theorems/01b36efc-13f7-5cac-b8c6-c004c4e112c6
-- title:
--   q-expansion of the ℓ-degeneracy Hecke multiplier
-- statement:
--   Fix a prime $p$ with $5 \le p$, a level $N \ge 1$, and an algebraically closed field $K$ of characteristic $p$ with decidable equality such that $N \ne 0$ in $K$; fix also a prime $\ell$ with $\ell \nmid N$ and $\ell \ne 0$ in $K$ (routine typeclass hypotheses are summarised here). Inside the Laurent series field $K(\!(q)\!)$ let $j(q)$ denote `jqModC K`, the series $q^{-1}$ times the mod-$p$ reduction of $E_4^3 \eta^{-24}$, let `qExpand K n` be the substitution $q \mapsto q^n$, and let $\theta = q\,\frac{d}{dq}$ be the operator `thetaL K`, $f \mapsto q \cdot f'$. The element `heckeMultiplier N K ℓ` lies in the intermediate field `charLDegeneracyRoof K N ℓ` generated over $K$ by $j(q)$, $j(q^N)$, $j(q^\ell)$ and $j(q^{N\ell})$, and is characterised by the property that in the module of Kähler differentials of that field over $K$ one has $d\bigl(j(q^\ell)\bigr) = h \cdot \alpha^{*}\bigl(d\,j(q)\bigr)$, where $\alpha^{*}$ is induced by the inclusion of the level-$N$ modular function field $K(j(q), j(q^N))$. The assertion is that, as Laurent series over $K$, the image $h$ of this multiplier satisfies $$h \cdot \theta j(q) = \ell \cdot (\theta j)(q^{\ell}).$$
--
--   This is the chain-rule reading of the defining relation of the degeneracy multiplier: it transfers the multiplier from the language of Kähler differentials to that of $q$-expansions, whence $h = \ell\, q^{1-\ell} + \cdots$. It is used in the study of the supersingular Hecke operator at level $N$ in characteristic $p$, both for the order and width computations at the places in a fibre and for the semilinearity of the Hecke action on the relevant Riemann–Roch spaces.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_SSHeckeV2_coe_heckeMultiplier_mul_thetaL_eq_smul_qExpand_of_ne_zero.lean

import Mathlib
import Definitions.Def_ModularCurve_SSHeckeV2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open AlgebraicCurve ModularCurve

theorem ModularCurve.SSHeckeV2.coe_heckeMultiplier_mul_thetaL_eq_smul_qExpand_of_ne_zero
    (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (K : Type) [Field K] [CharP K p] [IsAlgClosed K] [DecidableEq K] (N : ℕ) [NeZero N]
    (hN : (N : K) ≠ 0) (ℓ : ℕ) [Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N) (hℓK : (ℓ : K) ≠ 0) :
    ((ModularCurve.heckeMultiplier N K ℓ : ↥(charLDegeneracyRoof K N ℓ)) : LaurentSeries K) * thetaL K (jqModC K)
      = (ℓ : K) • qExpand K ℓ (thetaL K (jqModC K)) := by sorry
