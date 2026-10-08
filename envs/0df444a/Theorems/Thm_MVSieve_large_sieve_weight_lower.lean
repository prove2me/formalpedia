-- Prove2me | Theorems.Thm_MVSieve_large_sieve_weight_lower
-- name    : MVSieve.large_sieve_weight_lower
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-06T04:38:54.705676+00:00
-- url     : https://prove2.me/theorems/c26d5c10-63fc-44e8-ac6d-8a07beb2ffce
-- title:
--   Lower bound for the weights of the multiplicative large sieve
-- statement:
--   Let $Q\ge1$ and $N\ge 16Q^2$ be integers and let $1\le r\le Q$. Then
--   $$N\sum_{\substack{m\le Q/r\\ (m,r)=1,\ m\ \text{squarefree}}}\frac{r}{\varphi(r)\,\varphi(m)\,\bigl(N+16\,rmQ\bigr)}\ \ge\ \log\frac{Q}{r}-\log 4 .$$
--
--   The left side is $N$ times the weight attached to the primitive characters modulo $r$ in the weighted multiplicative large sieve `MVSieve.primitive_character_large_sieve`. The bound says that weight is essentially $\log(Q/r)/N$. This is the analogue, for the large-sieve constant $16$, of Montgomery and Vaughan's Lemmas 3 and 8. Riesel and Vaughan use those in the form
--   $$\frac{r}{\varphi(r)}\sum_{\substack{m\le z/r\\(m,r)=1}}\frac{\mu^2(m)}{\varphi(m)}\,\frac{1}{1+rm/z}>0.361+\log\frac{z}{r}.$$
--   Here the additive constant is $-\log 4$ instead of $0.361$, which costs nothing in the large-$x$ applications. Together, the two theorems bound the primitive character sums $\sum_{r}(\log(Q/r)-\log 4)\sum_\chi^*|\sum a_n\chi(n)|^2\le N\sum|a_n|^2$.
--
--   Formalization note: $m$ ranges over `Finset.Icc 1 Q` filtered by $rm\le Q$, `Nat.Coprime r m` and `Squarefree m`, the same index set as in `MVSieve.primitive_character_large_sieve`; $r,Q$ are positive naturals (`ℕ+`).
-- source:
--   H. L. Montgomery and R. C. Vaughan, The large sieve, Mathematika 20 (1973) 119–134, Lemmas 3 and 8; used in H. Riesel and R. C. Vaughan, On sums of primes, Ark. Mat. 21 (1983) 45–74, proof of Lemma 13, p. 66 (the inequality preceding (8.18)).

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Nat.Totient
import Mathlib.Data.PNat.Interval

theorem MVSieve.large_sieve_weight_lower (Q : ℕ+) (N : ℕ) (hN : 16 * (Q : ℕ) ^ 2 ≤ N)
    (r : ℕ+) (hr : r ≤ Q) :
    Real.log (((Q : ℕ) : ℝ) / ((r : ℕ) : ℝ)) - Real.log 4 ≤
      (N : ℝ) * ∑ m ∈ (Finset.Icc 1 (Q : ℕ)).filter
          (fun m => (r : ℕ) * m ≤ Q ∧ Nat.Coprime r m ∧ Squarefree m),
        ((r : ℕ) : ℝ) / (((r : ℕ).totient : ℝ) * (m.totient : ℝ) *
          ((N : ℝ) + 16 * (((r : ℕ) * m : ℕ) : ℝ) * ((Q : ℕ) : ℝ))) := by sorry
