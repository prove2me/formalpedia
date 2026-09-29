-- Prove2me | Theorems.Thm_ModularCurve_sharpUnitNecessary_of_prime
-- name    : ModularCurve.sharpUnitNecessary_of_prime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.618386+00:00
-- url     : https://prove2.me/theorems/7f0ecef6-1452-5b71-a13f-018dcf34704c
-- title:
--   `SharpUnitNecessary` at primes ℓnot≡ 1 (mod 12)
-- statement:
--   Let $\ell$ be a prime with $\ell \not\equiv 1 \pmod{12}$. Then [`ModularCurve.SharpUnitNecessary ℓ`](def/ModularCurve_EtaQuotient.html#L100) holds, that is: for every natural number $m$ and every function $H \colon \mathfrak H \to \mathbb C$ on the upper half-plane such that $m > 0$, $H$ is continuous, $H(\tau)^{\ell-1} = \bigl(\Delta(\tau)/\Delta(\mathrm{heckeDiagMatrix}(\ell)\cdot\tau)\bigr)^{m}$ for all $\tau \in \mathfrak H$, where $\Delta$ is `ModularForm.discriminant` and `heckeDiagMatrix ℓ` is, for $\ell \neq 0$, the upper triangular element of $\mathrm{GL}_2(\mathbb R)$ with entries $\ell, 0, 1$ (so that its action is $\tau \mapsto \ell\tau$), and such that $H(\gamma \cdot \tau) = H(\tau)$ for every $\gamma \in \Gamma_0(\ell)$ and every $\tau$, one has that `eisensteinNumerator ℓ`, namely the natural number $(\ell-1)/\gcd(\ell-1,12)$, divides $m$. Note that the exponent $\ell - 1$ and the quantity $\ell - 1$ inside the numerator are natural-number subtractions.
--
--   This is the necessity half of the statement that the Eisenstein numerator $(\ell-1)/\gcd(\ell-1,12)$ governs which powers of $\Delta(\tau)/\Delta(\ell\tau)$ admit a continuous $\Gamma_0(\ell)$-invariant $(\ell-1)$-st root, i.e. the sharpness of the order of the classical $\eta$-quotient modular unit on $X_0(\ell)$. It feeds the general statement [`ModularCurve.sharpUnitNecessary`](thm.html#ModularCurve.sharpUnitNecessary).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_sharpUnitNecessary_of_prime.lean

import Definitions.Def_ModularCurve_EtaQuotient
import Definitions.Def_NumberTheory_DedekindSum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.sharpUnitNecessary_of_prime (ℓ : ℕ) [Fact (Nat.Prime ℓ)] (h : ℓ % 12 ≠ 1) : ModularCurve.SharpUnitNecessary ℓ := by sorry
