-- Prove2me | Theorems.Thm_ModularCurve_sharpUnitInvariant
-- name    : ModularCurve.sharpUnitInvariant
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.618386+00:00
-- url     : https://prove2.me/theorems/234719a8-e121-53a4-984a-afd5ab4480f7
-- title:
--   Γ₀(ℓ)-invariance of the sharp eta quotient
-- statement:
--   Let $\ell$ be a natural number which is nonzero (the typeclass `NeZero ℓ`). The assertion is the predicate [`ModularCurve.SharpUnitInvariant ℓ`](def/ModularCurve_EtaQuotient.html#L97), which unfolds as follows: for every $\gamma$ in the congruence subgroup $\Gamma_0(\ell)$ and every point $\tau$ of the upper half plane, $$\mathrm{sharpUnitFun}\,\ell\,(\gamma\cdot\tau)=\mathrm{sharpUnitFun}\,\ell\,\tau,$$ where [`ModularCurve.sharpUnitFun ℓ`](def/ModularCurve_EtaQuotient.html#L73) is the function sending $\tau$ to $$\left(\frac{\eta(\tau)}{\eta\big(\mathrm{heckeDiagMatrix}\,\ell\cdot\tau\big)}\right)^{\mathrm{sharpExp}\,\ell},$$ the quotient of the Dedekind eta function evaluated at $\tau$ by its value at the translate of $\tau$ under the action of the matrix [`ModularForm.heckeDiagMatrix ℓ`](def/ModularForm_HeckeOperator.html#L21), raised to the integer exponent [`ModularCurve.sharpExp ℓ`](def/ModularCurve_EtaQuotient.html#L16). Thus the theorem states that this eta quotient is invariant under the full action of $\Gamma_0(\ell)$ on the upper half plane, for every level $\ell\ge 1$, with no primality or other arithmetic hypothesis on $\ell$. The proof cites the transformation law of $\eta$ under $\mathrm{SL}_2(\mathbb{Z})$ with positive lower-left entry (in terms of Dedekind sums), the behaviour of $\eta$ under integral translations, and a congruence modulo $\gcd(\ell-1,12)$ for the relevant combination of Dedekind sums at levels $c'$ and $\ell c'$.
--
--   This is the classical criterion, going back to Newman and Ligozat, that the eta quotient $(\eta(\tau)/\eta(\ell\tau))^{24/\gcd(\ell-1,12)}$ is a modular unit on $X_0(\ell)$, invariant under $\Gamma_0(\ell)$. It supplies the invariance input used in the Eisenstein-ideal computations, being cited by [`CuspForm.exists_qIntegral_qCoeff_congr_sigmaPrimeTo_eisensteinNumerator`](thm.html#CuspForm.exists_qIntegral_qCoeff_congr_sigmaPrimeTo_eisensteinNumerator) and by [`ModularCurve.isPrincipal_eisensteinNumerator_smul_cuspidalDivisor`](thm.html#ModularCurve.isPrincipal_eisensteinNumerator_smul_cuspidalDivisor).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_sharpUnitInvariant.lean

import Definitions.Def_ModularCurve_EtaQuotient
import Definitions.Def_NumberTheory_DedekindSum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.sharpUnitInvariant (ℓ : ℕ) [NeZero ℓ] : ModularCurve.SharpUnitInvariant ℓ := by sorry
