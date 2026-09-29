-- Prove2me | Theorems.Thm_ModularCurve_sharpUnitNecessary
-- name    : ModularCurve.sharpUnitNecessary
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.618386+00:00
-- url     : https://prove2.me/theorems/b89f5bda-2164-5316-be22-7ebfdd1394d2
-- title:
--   Necessity in the sharp-unit criterion at prime level ℓ
-- statement:
--   For every prime $\ell$ the predicate [`ModularCurve.SharpUnitNecessary`](def/ModularCurve_EtaQuotient.html#L100) holds at $\ell$, that is: for every natural number $m$ and every function $H \colon \mathbb{H} \to \mathbb{C}$ on the upper half-plane such that $m > 0$, $H$ is continuous, $H$ satisfies the power relation
--   $$H(\tau)^{\ell-1} = \Bigl(\frac{\Delta(\tau)}{\Delta(\mathrm{heckeDiagMatrix}(\ell)\cdot\tau)}\Bigr)^{m} \qquad (\tau \in \mathbb{H}),$$
--   where $\Delta$ is `ModularForm.discriminant` and [`ModularForm.heckeDiagMatrix`](def/ModularForm_HeckeOperator.html#L21) $\ell$ is the element of $\mathrm{GL}_2(\mathbb{R})$ given by the upper triangular matrix with diagonal entries $\ell$ and $1$ and off-diagonal entry $0$ (so that the denominator is $\Delta(\ell\tau)$ up to the chosen action), and such that $H$ is invariant under the action of every element of $\Gamma_0(\ell)$, i.e. $H(\gamma\cdot\tau) = H(\tau)$ for all $\gamma \in \mathrm{Gamma0}(\ell)$ and all $\tau \in \mathbb{H}$, one has that `eisensteinNumerator` $\ell = (\ell-1)/\gcd(\ell-1,12)$ divides $m$. The exponent $\ell - 1$ and the quantity $\ell - 1$ inside the numerator are natural-number subtractions.
--
--   This is the necessity half of the eta-quotient (sharp-unit) criterion at prime level: the numerator $n(\ell)$ of $(\ell-1)/12$ is a lower bound for the exponents $m$ for which an $(\ell-1)$-st root of $(\Delta(\tau)/\Delta(\ell\tau))^m$ can be made $\Gamma_0(\ell)$-invariant, the arithmetic input behind the exact order of the cuspidal divisor class of $J_0(\ell)$. It is used in the $q$-expansion congruence [`CuspForm.exists_qIntegral_qCoeff_congr_sigmaPrimeTo_eisensteinNumerator`](thm.html#CuspForm.exists_qIntegral_qCoeff_congr_sigmaPrimeTo_eisensteinNumerator).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_sharpUnitNecessary.lean

import Definitions.Def_ModularCurve_EtaQuotient

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.sharpUnitNecessary (ℓ : ℕ) [Fact (Nat.Prime ℓ)] : ModularCurve.SharpUnitNecessary ℓ := by sorry
