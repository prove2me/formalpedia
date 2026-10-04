-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_three_is_quadratic_nonresidue_mod_euler_prime
-- name    : OddPerfectNumber.Kernel.three_is_quadratic_nonresidue_mod_euler_prime
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-02T11:59:12.02637+00:00
-- url     : https://prove2.me/theorems/f113d40e-0f12-4cf8-b675-3cc5b49799c7
-- title:
--   For $p \equiv 5 \pmod{12}$ the prime $3$ is a quadratic nonresidue modulo $p$
-- statement:
--   If $p$ is a prime with $p \equiv 1 \pmod 4$ and $p \equiv 2 \pmod 3$, equivalently $p \equiv 5 \pmod{12}$, then $3$ is a quadratic nonresidue modulo $p$.
--
--   By quadratic reciprocity, since $p \equiv 1 \pmod 4$ the symbol is symmetric, so $\left(\frac{3}{p}\right) = \left(\frac{p}{3}\right)$. Euler's criterion gives $\left(\frac{p}{3}\right) = p^{(3-1)/2} = p \bmod 3 = -1$, because $p \equiv 2 \equiv -1 \pmod 3$.
--
--   **Consequence for the $k=5$ two-prime residual.** The proved theorem
--   `sigma_source_of_p_is_fourth_power_residue` says that any prime $t$ supplying $p$ in the second Dris equation satisfies $t^{(p-1)/4} = 1$ in $\mathbb{Z}/p$, so $t$ is in particular a quadratic residue modulo $p$. Taking $t = 3$ contradicts this theorem, and therefore
--
--   $$p \nmid \sigma\bigl(3^{2e}\bigr) \quad \text{for every } e \ge 0.$$
--
--   This matters because the first Dris equation forces $3 \mid m$ in the normalised two-prime branch, so without this exclusion the prime $3$ would look like a candidate supplier of the $p$-part of $\sigma(m^2) = p^5 s$. It removes the prime $3$ from the incoming $p$-valuation budget entirely, without ever claiming that $3 \nmid m$.

import Mathlib

namespace OddPerfectNumber.Kernel

/-- When `p` is prime with `p % 4 = 1` and `p % 3 = 2`, the Legendre symbol
  `legendreSym p 3` is `-1`: the prime `3` is a quadratic nonresidue modulo `p`.

  Quadratic reciprocity with `p = 1 (mod 4)` makes the symbol symmetric, and
  `p = 2 (mod 3)` evaluates `legendreSym p 3` as `-1`. -/
theorem three_is_quadratic_nonresidue_mod_euler_prime {p : Nat} [Fact p.Prime]
    (hp4 : p % 4 = 1) (hp3 : p % 3 = 2) :
    legendreSym p 3 = -1 := by
  sorry

end OddPerfectNumber.Kernel
