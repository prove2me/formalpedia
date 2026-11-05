-- Prove2me | Theorems.Thm_FowlerLSQC_Shor_factor_extraction
-- name    : FowlerLSQC.Shor.factor_extraction
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:36:07.134604+00:00
-- url     : https://prove2.me/theorems/da55fe71-6132-499e-8668-f509aba740c1
-- title:
--   Factors of $N$ from an even period
-- statement:
--   Let $N_1,N_2$ be primes and $N=N_1N_2$. Let $1<m<N$ with $\gcd(m,N)=1$, let $r$ be the period of $f(k)=m^k\bmod N$, and write $f(r/2)=m^{r/2}\bmod N$. If $r$ is even and $f(r/2)\ne N-1$, then
--   $$
--   \big\{\gcd(f(r/2)+1,N),\ \gcd(f(r/2)-1,N)\big\}=\{N_1,N_2\}.
--   $$
--
--   This is the classical step of Shor's algorithm that turns a period into the two prime factors of $N$.
--
--   **Formalization Note** The conclusion is an equality of finite sets. $f(r/2)\ge1$ because $m$ is a unit modulo $N$, so $f(r/2)-1$ is an ordinary natural number.
--
--   Differences from the source:
--   - reading: "the factors are $N_1=\gcd(f(r/2)+1,N)$ and $N_2=\gcd(f(r/2)-1,N)$" → the unordered set equality $\{\gcd(f(r/2)+1,N),\gcd(f(r/2)-1,N)\}=\{N_1,N_2\}$; reason: the two primes play symmetric roles and Fig. 7.1 (p.77) assigns the labels the other way round, so the assignment is a naming, not a claim
-- source:
--   Fowler, Towards Large-Scale Quantum Computation, arXiv:quant-ph/0506126v1, Ch. 7, p.75 (PDF p.93)

import Mathlib
import Definitions.Def_FowlerLSQC_Shor_period

namespace FowlerLSQC.Shor

/-- Factor extraction from an even period, Fowler, *Towards Large-Scale Quantum Computation*,
arXiv:quant-ph/0506126v1, Ch. 7, p.75 (PDF 93): let `N = N₁N₂` be a product of primes,
`1 < m < N`, `gcd(m, N) = 1`, and `r` the period of `f(k) = m^k mod N`. "Provided r is even and
f(r/2) ≠ N − 1, the factors are N1 = gcd(f(r/2) + 1, N) and N2 = gcd(f(r/2) − 1, N)."

**Formalization Note** The conclusion is the equality of unordered sets
`{gcd(f(r/2) + 1, N), gcd(f(r/2) − 1, N)} = {N₁, N₂}`: the labels are not determined by the two
primes (Fig. 7.1, p.77, assigns them the other way round). `f(r/2)` is `m^(r/2) % N`; it is at
least `1` because `m` is a unit, so the `ℕ` subtraction `f(r/2) − 1` never truncates. The primes
may coincide and may be `2`, as the book's setting allows. -/
theorem factor_extraction (N₁ N₂ N m : ℕ) (hN₁ : N₁.Prime) (hN₂ : N₂.Prime) (hN : N = N₁ * N₂)
    (hm1 : 1 < m) (hmN : m < N) (hcop : Nat.Coprime m N) (heven : Even (period N m))
    (hne : m ^ (period N m / 2) % N ≠ N - 1) :
    ({Nat.gcd (m ^ (period N m / 2) % N + 1) N, Nat.gcd (m ^ (period N m / 2) % N - 1) N} :
      Finset ℕ) = {N₁, N₂} := by sorry

end FowlerLSQC.Shor
