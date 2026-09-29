-- Prove2me | Theorems.Thm_ModularCurve_addOrderOf_cuspidalClass_eq_eisensteinNumerator
-- name    : ModularCurve.addOrderOf_cuspidalClass_eq_eisensteinNumerator
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.598281+00:00
-- url     : https://prove2.me/theorems/a7292d8a-85d1-57f1-9095-c78764bd199b
-- title:
--   Order of the cuspidal class on X₀(ℓ)
-- statement:
--   Let $\ell$ be a prime. Two hypotheses on $\ell$ are assumed. First, [`ModularCurve.SharpUnitInvariant ℓ`](def/ModularCurve_EtaQuotient.html#L97): the function $\tau \mapsto \bigl(\eta(\tau)/\eta(\delta_\ell\tau)\bigr)^{\mathrm{sharpExp}(\ell)}$ on the upper half-plane, where $\delta_\ell$ is the diagonal-type matrix [`ModularForm.heckeDiagMatrix ℓ`](def/ModularForm_HeckeOperator.html#L21) (upper triangular with entries $\ell,0,1$), is invariant under the action of every element of $\Gamma_0(\ell)$. Second, [`ModularCurve.SharpUnitNecessary ℓ`](def/ModularCurve_EtaQuotient.html#L100): for every $m>0$ and every continuous $H:\mathbb{H}\to\mathbb{C}$ satisfying $H(\tau)^{\ell-1} = \bigl(\Delta(\tau)/\Delta(\delta_\ell\tau)\bigr)^m$ for all $\tau$ and $H(\gamma\tau)=H(\tau)$ for all $\gamma\in\Gamma_0(\ell)$, one has $(\ell-1)/\gcd(\ell-1,12) \mid m$. The conclusion is that the additive order of the cuspidal class [`ModularCurve.cuspidalClass ℓ`](def/ModularCurve_CuspidalClass.html#L49) — the class, in the group of degree-zero divisors modulo principal divisors attached to the modular function field of level $\ell$ over $\overline{\mathbb{Q}}$, of the divisor $(\bar 0) - (\bar\infty)$ — equals [`ModularCurve.eisensteinNumerator ℓ`](def/ModularCurve_ModularUnit.html#L169), namely $(\ell-1)/\gcd(\ell-1,12)$.
--
--   This is Ogg's determination of the order of the cuspidal divisor class on $X_0(\ell)$ for $\ell$ prime, the numerator of $(\ell-1)/12$. It feeds the congruence properties of $q$-expansion coefficients of cusp forms of prime level used later, via [`CuspForm.exists_qIntegral_qCoeff_congr_sigmaPrimeTo_eisensteinNumerator`](thm.html#CuspForm.exists_qIntegral_qCoeff_congr_sigmaPrimeTo_eisensteinNumerator).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_addOrderOf_cuspidalClass_eq_eisensteinNumerator.lean

import Definitions.Def_ModularCurve_EtaQuotient
import Definitions.Def_ModularCurve_CuspidalClass

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.addOrderOf_cuspidalClass_eq_eisensteinNumerator (ℓ : ℕ) [Fact (Nat.Prime ℓ)] (hW : ModularCurve.SharpUnitInvariant ℓ) (hWnec : ModularCurve.SharpUnitNecessary ℓ) : addOrderOf (ModularCurve.cuspidalClass ℓ) = ModularCurve.eisensteinNumerator ℓ := by sorry
