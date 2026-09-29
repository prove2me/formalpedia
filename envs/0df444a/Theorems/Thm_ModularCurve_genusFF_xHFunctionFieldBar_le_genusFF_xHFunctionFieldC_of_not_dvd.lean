-- Prove2me | Theorems.Thm_ModularCurve_genusFF_xHFunctionFieldBar_le_genusFF_xHFunctionFieldC_of_not_dvd
-- name    : ModularCurve.genusFF_xHFunctionFieldBar_le_genusFF_xHFunctionFieldC_of_not_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.414366+00:00
-- url     : https://prove2.me/theorems/984968e2-d661-5bea-99e0-ec12adae2dbb
-- title:
--   Genus of X_H(M) does not drop modulo ℓ∤ M
-- statement:
--   Fix a positive integer $M$ and a subgroup $H\le(\mathbb{Z}/M)^\times$, and let $\Gamma_H(M)$ denote [`CohCarrier.GammaH M H`](def/CohCarrier_Level.html#L133), the image under the inclusion $\Gamma_0(M)\hookrightarrow\mathrm{SL}_2(\mathbb{Z})$ of the preimage of $H$ under the homomorphism `gamma0Units M`. Let $\ell$ be a prime not dividing $M$ and let $k$ be an algebraically closed field of characteristic $\ell$. Two function fields of one variable are compared. On the characteristic-$\ell$ side, [`ModularCurve.xHFunctionFieldC k M H`](def/ModularCurve_XH.html#L76) is the intermediate field of the Laurent series field $k((q))$ generated over $k$ by the set [`ModularCurve.intFormRatiosC k (CohCarrier.GammaH M H)`](def/ModularCurve_X1.html#L83) attached to $\Gamma_H(M)$. On the characteristic-zero side, [`ModularCurve.xHFunctionFieldBar M H`](def/ModularCurve_XH.html#L123) is the subfield of $\overline{\mathbb{Q}}((q))$ generated over $\overline{\mathbb{Q}}$ by the image of the corresponding subfield of $\mathbb{Q}((q))$, namely the field generated over $\mathbb{Q}$ by [`ModularCurve.intFormRatiosC`](def/ModularCurve_X1.html#L83) $\mathbb{Q}$ $\Gamma_H(M)$, under the coefficientwise embedding $\mathbb{Q}((q))\to\overline{\mathbb{Q}}((q))$. The assertion is the inequality of genera $$\mathrm{genusFF}_{\overline{\mathbb{Q}}}\bigl(\mathrm{xHFunctionFieldBar}\ M\ H\bigr)\ \le\ \mathrm{genusFF}_{k}\bigl(\mathrm{xHFunctionFieldC}\ k\ M\ H\bigr),$$ where for a field extension $F/K$ the genus `genusFF K F` is the $K$-dimension of $H^1$ of the zero divisor, divisors being finitely supported $\mathbb{Z}$-valued functions on the places of $F$ over $K$.
--
--   This is one half of Igusa's theorem that the modular curve $X_H(M)$ has good reduction at primes not dividing the level, stated in the language of $q$-expansion function fields: the genus in characteristic zero is bounded by the genus of the characteristic-$\ell$ function field. It is combined with the reverse inequality in [`ModularCurve.genusFF_xHFunctionFieldC_eq_genusFF_xHFunctionFieldBar_of_not_dvd`](thm.html#ModularCurve.genusFF_xHFunctionFieldC_eq_genusFF_xHFunctionFieldBar_of_not_dvd) to give equality of the two genera.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_genusFF_xHFunctionFieldBar_le_genusFF_xHFunctionFieldC_of_not_dvd.lean

import Mathlib
import Definitions.Def_ModularCurve_XH
import Definitions.Def_AlgebraicCurve_Repartitions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve ModularCurve

theorem ModularCurve.genusFF_xHFunctionFieldBar_le_genusFF_xHFunctionFieldC_of_not_dvd
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) {ℓ : ℕ} [Fact ℓ.Prime] (hℓM : ¬ ℓ ∣ M)
    (k : Type*) [Field k] [IsAlgClosed k] [CharP k ℓ] :
    genusFF (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) ≤
      genusFF k (ModularCurve.xHFunctionFieldC k M H) := by sorry
