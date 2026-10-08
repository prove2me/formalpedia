-- Prove2me | Theorems.Thm_KellyReversibility_Symmetric_eq_3_16_3_17_marginals
-- name    : KellyReversibility.Symmetric.eq_3_16_3_17_marginals
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T02:51:13.383185+00:00
-- url     : https://prove2.me/theorems/8f58b7cc-dc86-4470-9529-9bd27b666b70
-- title:
--   Eqs. (3.16)–(3.17) — number in queue and position classes under (3.14)
-- statement:
--   In the symmetric queue with gamma service requirements of Eq. (3.14) (class-$c$ customers arrive at rate $\nu(c)$ and need $w(c)$ exponential stages of mean $d(c)$), let $\pi(\mathbf c) = b \prod_{l=1}^n \nu(c(l)) d(c(l))/\phi(l)$ with $a = \sum_c \nu(c) d(c) w(c)$ and $b^{-1} = \sum_{n \ge 0} a^n / \prod_{l=1}^n \phi(l)$ convergent. Then:
--
--   1. the probability that there are $n$ customers in the queue is
--   $$\frac{b\,a^n}{\prod_{l=1}^n \phi(l)}; \tag{3.16}$$
--   2. given there are $n$ customers, $\mathbf c(1), \dots, \mathbf c(n)$ are independent, the customer in position $l$ is of class $c$ with probability
--   $$\frac{\nu(c)\, d(c)\, w(c)}{a}, \tag{3.17}$$
--   and $u(l)$ is equally likely to be any value in $1 \le u(l) \le w(c(l))$.
--
--   Part 2 is stated as the factorization, for every state $\mathbf c$ with $n$ customers,
--   $$\pi(\mathbf c) = \frac{b\,a^n}{\prod_{l=1}^n \phi(l)} \prod_{l=1}^n \frac{\nu(c(l))\,d(c(l))\,w(c(l))}{a}\cdot\frac{1}{w(c(l))}.$$
--
--   These marginals depend on $d(c)$ and $w(c)$ only through the mean service requirement $d(c)w(c)$.
--
--   **Formalization Note** Same model and hypotheses as the item for (3.14). Statement 1 is a convergent sum over the states with $n$ customers.
-- source:
--   Kelly, Reversibility and Stochastic Networks, Wiley 1979, p. 75 (PDF p. 78), Eqs. (3.16)–(3.17)

import Mathlib
import Definitions.Def_KellyReversibility_Symmetric_SymmetricQueue

namespace KellyReversibility.Symmetric

/-- Kelly 1979, p. 75, Eqs. (3.16)–(3.17): in the queue of (3.14) (no refinement), under the
distribution `π(c) = b ∏_{l=1}^n ν(c(l)) d(c(l)) / φ(l)` with `b` given by (3.15):
(3.16) the probability of `n` customers is `b a^n / ∏_{l=1}^n φ(l)`;
(3.17) given `n`, the records `c(1), …, c(n)` are independent, the customer in position `l` is
of class `c` with probability `ν(c) d(c) w(c) / a`, and `u(l)` is uniform on
`{1, …, w(c(l))}`.  The second part is stated as the factorization of `π(c)` into the
probability of `n` and these conditional probabilities. -/
theorem eq_3_16_3_17_marginals {C : Type*} [Countable C] (Q : SymmetricQueue C Unit)
    (hQ : Q.IsValid) (a : ℝ) (ha : HasSum (fun c => Q.ν c * Q.d c () * (Q.w c () : ℝ)) a)
    (b : ℝ) (hb : HasSum (fun n : ℕ => a ^ n / ∏ l ∈ Finset.Icc 1 n, Q.φ l) b⁻¹) :
    let π : Q.State → ℝ := fun x => b * ∏ i : Fin x.1.length,
      Q.ν (x.1.get i).cls * Q.d (x.1.get i).cls () / Q.φ ((i : ℕ) + 1)
    (∀ n : ℕ, HasSum (fun x : Q.State => if x.1.length = n then π x else 0)
        (b * a ^ n / ∏ l ∈ Finset.Icc 1 n, Q.φ l)) ∧
    (∀ x : Q.State, π x =
        b * a ^ x.1.length / (∏ l ∈ Finset.Icc 1 x.1.length, Q.φ l) *
          ∏ i : Fin x.1.length,
            (Q.ν (x.1.get i).cls * Q.d (x.1.get i).cls () * (Q.w (x.1.get i).cls () : ℝ) / a) *
              (1 / (Q.w (x.1.get i).cls () : ℝ))) := by sorry

end KellyReversibility.Symmetric
