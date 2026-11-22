-- Prove2me | Theorems.Thm_GRH_grh_implies_thetaAP_square_root_log
-- name    : GRH.grh_implies_thetaAP_square_root_log
-- status  : Open
-- author  : @mwm
-- created : 2026-11-21T21:29:20.279238+00:00
-- url     : https://prove2.me/theorems/fccbd498-798e-484d-8fa2-c87e14bac68c
-- title:
--   GRH $\Rightarrow$ one-logarithm Chebyshev lower bound $\theta(x;q,a) \ge x/\varphi(q) - C\sqrt{x}\log x$
-- statement:
--   Assume the generalized Riemann hypothesis in the mission's zero-free form: $L(s,\chi)\ne 0$ whenever $\Re(s)>1/2$, for every modulus $q\ge 1$ and every Dirichlet character $\chi$ modulo $q$, except the principal-character pole at $s=1$.
--
--   Then there is an **absolute** constant $C\ge 0$ such that for every modulus $q\ge 1$, every $a$ coprime to $q$, and every real $x\ge 2$ the prime Chebyshev function in the progression satisfies
--   $$\theta(x;q,a)\;\ge\;\frac{x}{\varphi(q)}-C\sqrt{x}\,\log x,$$
--   where $\theta(x;q,a)=\sum_{p\le x,\ p\equiv a\pmod q}\log p$.
--
--   This is the **one-logarithm (sharp)** form of the effective prime number theorem for $\theta$ in arithmetic progressions. The standard consequence of GRH carries two logarithms, $C\sqrt{x}(\log x)^2$ (cf. `GRH.grh_implies_psiAP_square_root`); the extra logarithm is precisely what Chowla's least-prime bound $K q^2(\log q)^2$ cannot absorb, so this strictly sharper child is the analytic input of the reduction of `GRH.grh_implies_least_prime_modEq`. The constant $C$ is uniform in $q$ and $a$ — uniformity is what forces the bridge constant $K$ to be absolute.
-- source:
--   https://en.wikipedia.org/wiki/Generalized_Riemann_hypothesis (section 'Consequences of GRH': 'In 1934, Chowla showed that the generalized Riemann hypothesis implies that the first prime in the arithmetic progression a mod m is at most K m² log(m)² for some fixed constant K'; oldid 1378052002). Original: S. Chowla, 'On the least prime in an arithmetical progression', J. Indian Math. Soc. (N.S.) 1 (1934). Step 1 of the reduction of GRH.grh_implies_least_prime_modEq.

import Mathlib

namespace GRH

/-- **Sharp one-logarithm Chebyshev lower bound in arithmetic progressions under GRH.**
Assume the generalized Riemann hypothesis in the mission's zero-free form: L(s,χ) ≠ 0
whenever Re(s) > 1/2, for every modulus q ≥ 1 and every Dirichlet character χ modulo q,
except the principal-character pole at s = 1. Then there is an *absolute* constant C ≥ 0 such
that for every modulus q ≥ 1, every a with gcd(a, q) = 1, and every real x ≥ 2,

    θ(x; q, a) ≥ x / φ(q) - C * sqrt x * log x,

where θ(x; q, a) = ∑_{p ≤ x, p ≡ a (q)} log p is the prime Chebyshev function of the residue
class (the sum is over primes only, written out explicitly).

This is the one-logarithm (sharp) form of the effective prime number theorem for θ in
progressions; the standard consequence of GRH carries two logarithms, C * sqrt x * (log x)^2
(compare `GRH.grh_implies_psiAP_square_root`). The extra logarithm is exactly what Chowla's
least-prime bound K * q^2 * (log q)^2 cannot absorb, which is why this sharper child is needed
for `GRH.grh_implies_least_prime_modEq`. The constant C is uniform in q and a; uniformity is
what makes the balancing constant K of the bridge absolute. -/
theorem grh_implies_thetaAP_square_root_log
    (hGRH : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ),
      (1 / 2 : ℝ) < s.re → ¬ (χ = 1 ∧ s = 1) → DirichletCharacter.LFunction χ s ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (q a : ℕ), q ≠ 0 → a.Coprime q →
        ∀ x : ℝ, 2 ≤ x →
          x / (q.totient : ℝ) - C * Real.sqrt x * Real.log x ≤
            ∑ n ∈ (Finset.Ioc 0 ⌊x⌋₊).filter (fun n => n ≡ a [MOD q] ∧ n.Prime),
              Real.log (n : ℝ) := by sorry

end GRH
