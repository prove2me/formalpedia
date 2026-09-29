-- Prove2me | Theorems.Thm_ModularCurve_thetaL_laurentMap_lambdaDworkQuotient
-- name    : ModularCurve.thetaL_laurentMap_lambdaDworkQuotient
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.908972+00:00
-- url     : https://prove2.me/theorems/0600e75e-2a92-5302-94ee-32d9a2db01d9
-- title:
--   A θ-identity for the Dwork quotient of λ
-- statement:
--   Let $q$ be a prime and let $S$ be a Laurent series with integer coefficients satisfying $\mathrm{qExpand}_{\mathbb Z,q}(\lambda) - \lambda^{q} = q\,S$, where $\lambda$ denotes the explicit integral Laurent series `lambdaInt` — the product of $\mathfrak q$ (the Hahn series `single 1 1`) with the eighth power of the eta product $\prod_{n\ge 1}(1-\mathfrak q^{\,n})$, the sixteenth power of that eta product with $\mathfrak q$ replaced by $\mathfrak q^{4}$, and the series `dedekindEtaUnitInv` with $\mathfrak q$ replaced by $\mathfrak q^{2}$ — and where `qExpand` $N$ is the ring endomorphism of Laurent series substituting $\mathfrak q \mapsto \mathfrak q^{N}$ (shifting exponents by multiplication by $N$). Let $k$ be a field of characteristic $q$, write $\bar{\;\cdot\;}$ for the coefficientwise reduction `laurentMap (Int.castRingHom k)` along $\mathbb Z \to k$, so that $\bar\lambda$ is `lambdaModC k`, and let $\theta = \mathrm{thetaL}_k$ be the $k$-linear operator $f \mapsto \mathfrak q\, f'$, whose effect on coefficients is $a_n \mapsto n\,a_n$. Then, in $k$-coefficient Laurent series, $$\theta(\bar S) = \big(\theta(\bar\lambda)\big)^{q} - \bar\lambda^{\,q-1}\,\theta(\bar\lambda),$$ the exponent $q-1$ being truncated natural subtraction.
--
--   The identity expresses the image mod $q$ of the Dwork quotient $S = \big(\lambda(\mathfrak q^{q}) - \lambda(\mathfrak q)^{q}\big)/q$ under the operator $\theta = \mathfrak q\,d/d\mathfrak q$ in terms of $\bar\lambda$ alone. It is used in the analysis of the Frobenius graph for the $\lambda$-series, being cited by [`ModularCurve.lambdaKroneckerRemainder_frobeniusGraph_ode`](thm.html#ModularCurve.lambdaKroneckerRemainder_frobeniusGraph_ode).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_thetaL_laurentMap_lambdaDworkQuotient.lean

import Mathlib
import Definitions.Def_ModularCurve_LambdaSeries
import Definitions.Def_ModularCurve_KroneckerTransport
import Definitions.Def_ModularCurve_QExpansionDiff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option autoImplicit false

open ModularCurve

theorem ModularCurve.thetaL_laurentMap_lambdaDworkQuotient
    (q : ℕ) [Fact q.Prime]
    (S : LaurentSeries ℤ) (hS : qExpand ℤ q lambdaInt - lambdaInt ^ q = (q : LaurentSeries ℤ) * S)
    (k : Type*) [Field k] [CharP k q] :
    thetaL k (laurentMap (Int.castRingHom k) S) =
      thetaL k (lambdaModC k) ^ q - lambdaModC k ^ (q - 1) * thetaL k (lambdaModC k) := by sorry
