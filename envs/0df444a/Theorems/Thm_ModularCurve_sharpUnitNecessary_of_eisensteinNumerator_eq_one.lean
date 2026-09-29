-- Prove2me | Theorems.Thm_ModularCurve_sharpUnitNecessary_of_eisensteinNumerator_eq_one
-- name    : ModularCurve.sharpUnitNecessary_of_eisensteinNumerator_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.618386+00:00
-- url     : https://prove2.me/theorems/2cd63d92-23d6-519e-a6bb-57bdc69b238a
-- title:
--   Necessity of the η-unit exponent when n(ℓ)=1
-- statement:
--   Let $\ell$ be a natural number and suppose that the quantity [`ModularCurve.eisensteinNumerator`](def/ModularCurve_ModularUnit.html#L169) $\ell$, defined as $(\ell-1)/\gcd(\ell-1,12)$ (natural-number subtraction and division), equals $1$. The conclusion is the predicate [`ModularCurve.SharpUnitNecessary`](def/ModularCurve_EtaQuotient.html#L100) $\ell$, which asserts: for every natural number $m$ and every function $H \colon \mathfrak{H} \to \mathbb{C}$ on the upper half plane such that $m > 0$, $H$ is continuous, $H(\tau)^{\ell-1} = \bigl(\Delta(\tau)/\Delta(A_\ell \cdot \tau)\bigr)^m$ for all $\tau \in \mathfrak{H}$, where $\Delta$ is `ModularForm.discriminant` and $A_\ell =$ [`ModularForm.heckeDiagMatrix`](def/ModularForm_HeckeOperator.html#L21) $\ell$ is the element of $\mathrm{GL}_2(\mathbb{R})$ given by the upper triangular matrix with diagonal entries $\ell, 1$ and upper right entry $0$ (hence acting by $\tau \mapsto \ell\tau$), taken to be the identity when $\ell = 0$, and such that $H(\gamma \cdot \tau) = H(\tau)$ for all $\gamma \in \Gamma_0(\ell)$ and all $\tau$, one has $(\ell-1)/\gcd(\ell-1,12) \mid m$. Thus under the hypothesis $(\ell-1)/\gcd(\ell-1,12) = 1$, equivalently $(\ell-1) \mid 12$ for $\ell \ge 1$, the divisibility conclusion is automatic.
--
--   This discharges the divisibility statement $n(\ell) \mid m$ for the exponent attached to the $\eta$-quotient modular unit on $X_0(\ell)$, in the range where the relevant numerator $n(\ell) = (\ell-1)/\gcd(\ell-1,12)$ is trivial. It is used by [`ModularCurve.sharpUnitNecessary_of_prime`](thm.html#ModularCurve.sharpUnitNecessary_of_prime), which assembles the general case from this degenerate case and the remaining ones.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_sharpUnitNecessary_of_eisensteinNumerator_eq_one.lean

import Definitions.Def_ModularCurve_EtaQuotient

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.sharpUnitNecessary_of_eisensteinNumerator_eq_one (ℓ : ℕ) (h : ModularCurve.eisensteinNumerator ℓ = 1) : ModularCurve.SharpUnitNecessary ℓ := by sorry
