-- Prove2me | Theorems.Thm_ModularCurve_SSHeckeV2_ssHeckeFun_smul
-- name    : ModularCurve.SSHeckeV2.ssHeckeFun_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.379182+00:00
-- url     : https://prove2.me/theorems/e5ff0866-015a-5ab5-8d40-c864a945d7cf
-- title:
--   Homogeneity of the supersingular Hecke operator
-- statement:
--   Fix a prime $p$ with $5 \le p$, an algebraically closed field $K$ of characteristic $p$, a positive integer $N$ with $(N : K) \neq 0$, a prime $\ell$ with $\ell \nmid N$ and $\ell \neq p$, an integer $k$, a scalar $c \in K$, and an element $v$ of $\mathrm{SSCarrier}\,p\,N\,K\,k$, that is, a $K$-valued function on the index type of pairs consisting of a place $x$ of the modular function field $\mathrm{modularFunctionFieldC}\ K\ N$ (the subfield of $K((q))$ generated over $K$ by the $q$-expansions $jq$ and $jq_N$) lying in $\mathrm{ssPlaces}\,p\,N\,K$ together with the conditions $2 \le k$, $2 \mid k$, $\mathrm{placeWidth}\,N\,x \mid k/2$ and $5 \le p$. The assertion is that the operator $\mathrm{ssHeckeFun}\,p\,N\,K\,k\,\ell$ commutes with scalars: $\mathrm{ssHeckeFun}(c \cdot v) = c \cdot \mathrm{ssHeckeFun}(v)$, the scalar action on carriers being pointwise multiplication in $K$. Here $\mathrm{ssHeckeFun}$ sends $v$ to the function whose value at $x$ is $\ell^{k/2 - 1}$ times the leading coefficient, at $x$ in the sense of $\mathrm{lead}$ with exponent $\mathrm{poleOrder}$, of the trace from the degeneracy roof field $\mathrm{charLDegeneracyRoof}\ K\ N\ \ell$ down to $\mathrm{modularFunctionFieldC}\ K\ N$ along $\mathrm{heckeAlphaC}$ of $\mathrm{heckeBetaC}(\mathrm{liftFun}\,v) \cdot \mathrm{heckeMultiplier}^{(k/2)}$, where $\mathrm{liftFun}\,v$ is a chosen modular function with prescribed pole bounds along the supersingular places and prescribed leading coefficients $v$.
--
--   This is the homogeneity half of the $K$-linearity of the Hecke operator $T_\ell$ acting on weight-$k$ supersingular value vectors; since $\mathrm{liftFun}$ is a choice of lift, the content is independence of the chosen lift together with $K$-linearity of the trace and of leading coefficients. It is used in the construction of the window form of $\mathrm{ssHeckeFun}$ and in the production of supersingular data over an algebraically closed field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_SSHeckeV2_ssHeckeFun_smul.lean

import Mathlib
import Definitions.Def_ModularCurve_SSCarrier
import Definitions.Def_ModularCurve_SSHeckeV2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
open AlgebraicCurve ModularCurve

theorem ModularCurve.SSHeckeV2.ssHeckeFun_smul (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (K : Type) [Field K] [CharP K p] [IsAlgClosed K] [DecidableEq K] (N : ℕ) [NeZero N]
    (hN : (N : K) ≠ 0) (ℓ : ℕ) [Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N) (hℓp : ℓ ≠ p)
    (k : ℤ) (c : K) (v : ModularCurve.SSCarrier p N K hp5 k) :
    ModularCurve.ssHeckeFun p N K hp5 k ℓ (c • v) = c • ModularCurve.ssHeckeFun p N K hp5 k ℓ v := by sorry
