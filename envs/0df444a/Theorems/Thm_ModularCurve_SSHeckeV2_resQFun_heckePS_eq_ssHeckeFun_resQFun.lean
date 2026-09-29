-- Prove2me | Theorems.Thm_ModularCurve_SSHeckeV2_resQFun_heckePS_eq_ssHeckeFun_resQFun
-- name    : ModularCurve.SSHeckeV2.resQFun_heckePS_eq_ssHeckeFun_resQFun
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.379182+00:00
-- url     : https://prove2.me/theorems/d090489c-9d61-5cdf-8308-95fe8b59e782
-- title:
--   Restriction to supersingular points intertwines T_ℓ with T_ℓ^{ss}
-- statement:
--   Fix a prime $p$ with $p\ge 5$ and an algebraically closed field $K$ of characteristic $p$, a nonzero natural number $N$ whose image in $K$ is nonzero, and a prime $\ell$ with $\ell\nmid N$ and $\ell\ne p$. Let $k\in\mathbb Z$ and let $\varphi$ be a power series over $K$ lying in [`ModPForms.modPMod N k K`](def/CuspForm_ModPForms.html#L12), the $K$-span of the power series $\sum_n \bar a_n q^n$ obtained by reducing integral sequences $(a_n)$ of $q$-expansion coefficients of weight-$k$ modular forms on $\Gamma_0(N)$; assume moreover that [`ModPForms.heckePS k ℓ φ`](def/CuspForm_ModPForms.html#L20), the power series with $n$-th coefficient $\mathrm{coeff}_{n\ell}(\varphi)+\ell^{k-1}\,\mathrm{coeff}_{n/\ell}(\varphi)$ when $\ell\mid n$ and $\mathrm{coeff}_{n\ell}(\varphi)$ otherwise, also lies in that span. The conclusion is an equality of functions on `SSIndex p N K hp5 k`: applying `resQFun` to $T_\ell\varphi$ — that is, sending an index $x$ to the value at $x$ of $u^{\,\mathrm{poleOrder}(x)}G$, where $u$ is the local uniformiser and $G$ is a chosen element of the modular function field `modularFunctionFieldC K N` whose Laurent expansion equals $\varphi\cdot\theta(j_q)^{-(k/2)}$ — agrees with `ssHeckeFun` applied to `resQFun` of $\varphi$, namely $x\mapsto \ell^{\,k/2-1}$ times the value at $x$ of $u^{\,\mathrm{poleOrder}(x)}$ times the trace from `charLDegeneracyRoof K N ℓ` to the modular function field of $\beta(\,\cdot\,)$ applied to the lift of `resQFun` $\varphi$, multiplied by the $(k/2)$-th power of `heckeMultiplier`. Here $k/2$ is integer division.
--
--   This is the $q$-expansion-level commutation of the classical coefficient Hecke operator $T_\ell$ with the Hecke operator on functions on supersingular points, i.e. the equivariance of the restriction map from mod-$p$ modular forms of weight $k$ and level $N$ to functions on the supersingular locus. It supplies the equivariance clause of the supersingular datum, and is cited by [`ModPForms.nonempty_ssDatum_algebraicClosure`](thm.html#ModPForms.nonempty_ssDatum_algebraicClosure).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_SSHeckeV2_resQFun_heckePS_eq_ssHeckeFun_resQFun.lean

import Mathlib
import Definitions.Def_ModularCurve_SSHeckeV2
import Definitions.Def_CuspForm_ModPForms

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
open AlgebraicCurve ModularCurve

theorem ModularCurve.SSHeckeV2.resQFun_heckePS_eq_ssHeckeFun_resQFun (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (K : Type) [Field K] [CharP K p] [IsAlgClosed K] [DecidableEq K] (N : ℕ) [NeZero N]
    (hN : (N : K) ≠ 0) (ℓ : ℕ) [Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N) (hℓp : ℓ ≠ p)
    (k : ℤ) (φ : PowerSeries K) (hφ : φ ∈ ModPForms.modPMod N k K) (hTφ : ModPForms.heckePS k ℓ φ ∈ ModPForms.modPMod N k K) :
    ModularCurve.resQFun p N K hp5 k (ModPForms.heckePS k ℓ φ) = ModularCurve.ssHeckeFun p N K hp5 k ℓ (ModularCurve.resQFun p N K hp5 k φ) := by sorry
