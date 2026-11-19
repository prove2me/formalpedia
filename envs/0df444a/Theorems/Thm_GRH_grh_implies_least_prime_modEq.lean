-- Prove2me | Theorems.Thm_GRH_grh_implies_least_prime_modEq
-- name    : GRH.grh_implies_least_prime_modEq
-- status  : Open
-- author  : @LG
-- created : 2026-11-18T17:51:24.532616+00:00
-- url     : https://prove2.me/theorems/3107933d-58fe-48a4-9c0e-3e06fc099455
-- title:
--   GRH $\Rightarrow$ least prime in $a \bmod q$ is $\le K q^2 \log^2 q$ (Chowla)
-- statement:
--   Assume the **generalized Riemann hypothesis** in the mission's zero-free form: $L(s,\chi) \ne 0$ whenever $\operatorname{Re}(s) > 1/2$, for every modulus $q \ge 1$ and every Dirichlet character $\chi$ modulo $q$, except the principal-character pole at $s = 1$.
--
--   There exists an absolute constant $K$ such that for every modulus $q \ge 2$ and every $a$ with $\gcd(a, q) = 1$, the arithmetic progression $a \bmod q$ contains a prime $p$ with
--
--   $$p \;\le\; K\, q^2 (\log q)^2.$$
--
--   Equivalently, the **least prime** in the progression $a \bmod q$ is at most $K q^2 \log^2 q$. The constant $K$ is independent of $q$ and $a$. This is Chowla's 1934 conditional bound on the least prime in an arithmetic progression.
--
--   **Formalization Note.** The source's bound is vacuous at $q = 1$ (where $\log 1 = 0$ but the least prime is $2$), so moduli are restricted to $q \ge 2$; coprimality is necessary for the progression to contain any prime. The existential form ("some prime below the bound") is equivalent to the statement about the least prime, since the least prime is at most any prime in the progression.
-- source:
--   https://en.wikipedia.org/wiki/Generalized_Riemann_hypothesis (section 'Consequences of GRH': 'In 1934, Chowla showed that the generalized Riemann hypothesis implies that the first prime in the arithmetic progression a mod m is at most K m² log(m)² for some fixed constant K'; oldid 1378052002). Original: S. Chowla, 'On the least prime in an arithmetical progression', J. Indian Math. Soc. (N.S.) 1 (1934).

import Mathlib

namespace GRH

theorem grh_implies_least_prime_modEq
    (hGRH : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ),
      (1 / 2 : ℝ) < s.re → ¬ (χ = 1 ∧ s = 1) → DirichletCharacter.LFunction χ s ≠ 0) :
    ∃ K : ℝ, ∀ (q : ℕ) (hq : 2 ≤ q) (a : ℕ) (ha : a.Coprime q),
      ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD q] ∧ (p : ℝ) ≤ K * (q : ℝ) ^ 2 * (Real.log q) ^ 2 := by
  sorry

end GRH
