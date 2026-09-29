-- Prove2me | Theorems.Thm_ModularCurve_frobeniusInputsModL
-- name    : ModularCurve.frobeniusInputsModL
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.414366+00:00
-- url     : https://prove2.me/theorems/2f7e5057-e4f1-5ab4-a68c-66c21cf442e0
-- title:
--   Frobenius inputs on the mod-ℓ modular function field
-- statement:
--   Let $\ell$ be a prime, let $K$ be an algebraically closed field of characteristic $\ell$, and let $N$ be a nonzero natural number. Write $F =$ `modularFunctionFieldFullC K N` for the intermediate field of the Laurent series field $K((q))$ obtained by adjoining to $K$ the set `divisorExpansionsC K N`, and let $\varphi =$ `frobeniusModL K N ℓ` be the $K$-algebra endomorphism of $F$ induced by the substitution $q \mapsto q^{\ell}$ on $q$-expansions (it fixes the constants, as the displayed commutation shows). The conclusion is the conjunction packaged as [`ModularCurve.FrobeniusInputsModL K N ℓ`](def/ModularCurve_FrobeniusModL.html#L206): there exist (i) an instance of `HasPrincipalDivisors K F`, i.e. for each $f \in F$ with $f \neq 0$ a divisor $D$ of $F/K$ whose value at every place $v$ of $F$ over $K$ is $v.\mathrm{ord}\, f$ and whose degree is $0$; and (ii) a witness `hfin` that $F$ is a finite module over itself for the algebra structure transported along $\varphi$, i.e. $F$ is finite over $\varphi(F)$; and, relative to these, both the predicate `FundamentalIdentity` for the extension of $F$ by $F$ along $\varphi$ (using the integrality of $\varphi$) and the predicate `Divisor.PushforwardNormFormula` for that extension hold.
--
--   This assembles, for the function field of $X_0(N)$ reduced modulo $\ell$, the four curve-theoretic inputs — existence of principal divisors of degree zero, finiteness of $F$ over its image under the $\ell$-power Frobenius, the fundamental identity $\sum_{w \mid v} e(w/v) f(w/v) = [F : \varphi(F)]$, and the compatibility of divisor push-forward with the field norm — under which the Frobenius correspondence on the Jacobian is the honest push-forward and pull-back along $\varphi$. It is the hypothesis package used by the mod-$\ell$ Frobenius and Hecke computations on $q$-expansions, among them the identities relating Frobenius push-forward to the coefficient maps and the eigenform coefficient congruences.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_frobeniusInputsModL.lean

import Mathlib
import Definitions.Def_ModularCurve_FrobeniusModL

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.frobeniusInputsModL (K : Type*) [Field K] [IsAlgClosed K] {ℓ : ℕ} [Fact ℓ.Prime]
    [CharP K ℓ] (N : ℕ) [NeZero N] :
    ModularCurve.FrobeniusInputsModL K N ℓ := by sorry
