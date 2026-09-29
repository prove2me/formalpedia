-- Prove2me | Theorems.Thm_ModularCurve_sharpUnitNecessary_of_mod_sixty_eq_thirteen
-- name    : ModularCurve.sharpUnitNecessary_of_mod_sixty_eq_thirteen
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.618386+00:00
-- url     : https://prove2.me/theorems/d021e719-6161-5ccd-85e4-32338e895448
-- title:
--   Sharp unit necessity at levels ℓ ≡ 13 (mod 60)
-- statement:
--   For every natural number $i$, the predicate [`ModularCurve.SharpUnitNecessary`](def/ModularCurve_EtaQuotient.html#L100) holds at $\ell = 60i+13$. Unfolding that predicate: for every natural number $m$ and every function $H \colon \mathfrak{H} \to \mathbb{C}$ on the upper half-plane such that $m > 0$, $H$ is continuous, $H(\tau)^{\ell - 1} = \bigl(\Delta(\tau)/\Delta(M_\ell \cdot \tau)\bigr)^{m}$ for all $\tau$, where $\Delta$ is `ModularForm.discriminant` and $M_\ell =$ [`ModularForm.heckeDiagMatrix`](def/ModularForm_HeckeOperator.html#L21) $\ell$ is the upper triangular element of $\mathrm{GL}_2(\mathbb{R})$ with entries $\ell, 0, 1$ (so that $M_\ell \cdot \tau = \ell\tau$), and such that $H(\gamma \cdot \tau) = H(\tau)$ for all $\gamma \in \Gamma_0(\ell)$ and all $\tau$, the conclusion is that [`ModularCurve.eisensteinNumerator`](def/ModularCurve_ModularUnit.html#L169) $\ell = (\ell - 1)/\gcd(\ell - 1, 12)$ divides $m$. For $\ell = 60i+13$ one has $\gcd(\ell-1,12) = 12$, so the divisor in question is $5i+1$. The exponent $\ell - 1$ and the quotient defining `eisensteinNumerator` are natural-number operations. The assertion covers the whole residue class $\ell \equiv 13 \pmod{60}$, composite levels included.
--
--   This is the necessity half of the statement that the $\eta$-quotient attached to $\Delta(\tau)/\Delta(\ell\tau)$ generates the group of modular units on $X_0(\ell)$ with the expected order of vanishing, in the form: any continuous $\Gamma_0(\ell)$-invariant $(\ell-1)$-st root of $(\Delta(\tau)/\Delta(\ell\tau))^m$ forces $(\ell-1)/\gcd(\ell-1,12) \mid m$. It supplies an infinite family of levels for the necessity predicate and is cited by [`ModularCurve.sharpUnitNecessary_of_mod_twelve_eq_one`](thm.html#ModularCurve.sharpUnitNecessary_of_mod_twelve_eq_one).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_sharpUnitNecessary_of_mod_sixty_eq_thirteen.lean

import Definitions.Def_ModularCurve_EtaQuotient
import Definitions.Def_NumberTheory_DedekindSum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.sharpUnitNecessary_of_mod_sixty_eq_thirteen (i : ℕ) : ModularCurve.SharpUnitNecessary (60 * i + 13) := by sorry
