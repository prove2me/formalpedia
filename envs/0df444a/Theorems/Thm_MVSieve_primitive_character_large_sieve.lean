-- Prove2me | Theorems.Thm_MVSieve_primitive_character_large_sieve
-- name    : MVSieve.primitive_character_large_sieve
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-06T04:19:49.935587+00:00
-- url     : https://prove2.me/theorems/5bb1a432-fc7e-439d-bf08-eb6878e1ab92
-- title:
--   Weighted large sieve for primitive Dirichlet characters (Riesel–Vaughan form, constant 16)
-- statement:
--   Let $Q\ge 1$ and $M,N\ge 0$ be integers, and let $a_n\in\mathbb C$ for $M\le n<M+N$. Assume every $n$ with $a_n\ne0$ has all of its prime factors larger than $Q$, so the coefficients live on integers coprime to every modulus $q\le Q$. Then
--   $$\sum_{r\le Q}\ \sum_{\substack{m\le Q/r\\ (m,r)=1,\ m\ \text{squarefree}}} \frac{r}{\varphi(r)\,\varphi(m)\,\bigl(N+16\,rmQ\bigr)}\ \sum_{\chi \bmod r}^{\ *}\Bigl|\sum_{M\le n<M+N} a_n\,\chi(n)\Bigr|^2\ \le\ \sum_{M\le n<M+N}|a_n|^2,$$
--   where $\sum^*$ runs over the primitive Dirichlet characters modulo $r$ (for $r=1$, the trivial character).
--
--   This is the weighted multiplicative large sieve in the form Riesel and Vaughan use in their treatment of Schnirelmann's constant: their (8.17) combined with the Gauss-sum decomposition that leads to (8.18). Here the Montgomery–Vaughan constant $3/2$ is replaced by $16$. The inner sum over $m$ is the sieve gain: by `MVSieve.large_sieve_weight_lower` it is about $\log(Q/r)/N$ when $N\ge16Q^2$. Applied to the indicator of primes in an interval, it bounds the non-principal character sums of primes on average over moduli.
--
--   Formalization note: $r$ ranges over `Finset.Icc 1 Q` in `ℕ+`; $m$ over `Finset.Icc 1 Q` filtered by $rm\le Q$, `Nat.Coprime r m`, `Squarefree m`; primitivity is written `χ.conductor = r`; $\chi(n)$ is $\chi$ applied to the image of $n$ in `ZMod r`.
-- source:
--   H. Riesel and R. C. Vaughan, On sums of primes, Ark. Mat. 21 (1983) 45–74, §8, eqs. (8.17)–(8.18) and the Gauss-sum computation between them, pp. 65–66; H. L. Montgomery and R. C. Vaughan, The large sieve, Mathematika 20 (1973) 119–134, (2.6). Weighted additive input: platform theorem WeightedHilbert_nonuniform_large_sieve_sixteen (ee72dd79-89b1-4fab-8700-1074eec4cacc).

import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Nat.Totient
import Mathlib.Data.PNat.Interval
import Mathlib.Analysis.Complex.Basic

theorem MVSieve.primitive_character_large_sieve (Q : ℕ+) (M N : ℕ) (a : ℕ → ℂ)
    (ha : ∀ n ∈ Finset.Ico M (M + N), a n ≠ 0 → ∀ p : ℕ, p.Prime → p ∣ n → (Q : ℕ) < p) :
    ∑ r ∈ Finset.Icc 1 Q, ∑ m ∈ (Finset.Icc 1 (Q : ℕ)).filter
        (fun m => (r : ℕ) * m ≤ Q ∧ Nat.Coprime r m ∧ Squarefree m),
      ((r : ℕ) : ℝ) / (((r : ℕ).totient : ℝ) * (m.totient : ℝ) *
          ((N : ℝ) + 16 * (((r : ℕ) * m : ℕ) : ℝ) * ((Q : ℕ) : ℝ))) *
        ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ r => χ.conductor = r),
          ‖∑ n ∈ Finset.Ico M (M + N), a n * χ n‖ ^ 2
      ≤ ∑ n ∈ Finset.Ico M (M + N), ‖a n‖ ^ 2 := by sorry
