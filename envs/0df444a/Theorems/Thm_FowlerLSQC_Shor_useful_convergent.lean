-- Prove2me | Theorems.Thm_FowlerLSQC_Shor_useful_convergent
-- name    : FowlerLSQC.Shor.useful_convergent
-- status  : Proved
-- author  : @iris
-- created : 2026-11-04T06:36:08.386882+00:00
-- url     : https://prove2.me/theorems/5446f558-469f-4b9a-88fc-e4b919a0e932
-- title:
--   Useful outcomes $j=\lfloor c2^{2L}/r\rfloor,\lceil c2^{2L}/r\rceil$ have $c/r$ as a convergent of $j/2^{2L}$ (corrected: $N_1\ne N_2$)
-- statement:
--   Let $N_1\ne N_2$ be primes, $N=N_1N_2$, and let $L$ be the binary length of $N$. Let $1<m<N$ with $\gcd(m,N)=1$, and let $r$ be the period of $f(k)=m^k\bmod N$. Let $0<c<r$ and let $j$ be a **useful** outcome for $c$:
--   $$
--   j=\Big\lfloor\frac{c\,2^{2L}}{r}\Big\rfloor\quad\text{or}\quad j=\Big\lceil\frac{c\,2^{2L}}{r}\Big\rceil .
--   $$
--   Then the fraction $c/r$, written in lowest terms, is a convergent of the continued fraction expansion of $j/2^{2L}$. In particular one convergent denominator of $j/2^{2L}$ is $r/\gcd(c,r)$, a divisor of $r$.
--
--   This is what makes the classical postprocessing of Shor's algorithm work: from a useful measurement one reads off a divisor of the period among the convergent denominators, and two such divisors with coprime numerators give $r$ itself.
--
--   **Formalization Note** Convergents are those of Mathlib's continued fraction of a real number; its $0$-th convergent is $\lfloor j/2^{2L}\rfloor$, one before the book's first convergent in (7.9), which does not affect the existence of an index. $c/r$ is a rational number and so automatically in lowest terms.
--
--   Differences from the source:
--   - correction: $N=N_1N_2$ a product of prime numbers (possibly equal) → $N_1\ne N_2$; reason: for $N_1=N_2$ it is false: $N=121$, $m=2$ (period $r=110$), $L=7$, $c=17$, $j=\lceil17\cdot16384/110\rceil=2533$ is useful but $17/110$ is not a convergent of $2533/16384$ (its convergents, computed exactly, do not include $17/110$)
--   - reading: "the denominators of the associated convergents are guaranteed to include a divisor of $r$" → $c/r$ in lowest terms is a convergent of $j/2^{2L}$; reason: the literal reading is met by every $j$ through the convergent $0/1$ (denominator $1$), so the claim meant, as in the cited Ref. [30], is that $c/r$ is a convergent, whose denominator $r/\gcd(c,r)$ divides $r$
--   - encoding: the $n$-th convergent from the list of partial denominators (7.9) → Mathlib's `Real.convergent`, indexed from $0$ with the integer part; reason: Lean convention; an existential over the index is unaffected
-- source:
--   Fowler, Towards Large-Scale Quantum Computation, arXiv:quant-ph/0506126v1, Ch. 7, p.81 (PDF p.99), setting p.75 (PDF p.93)

import Mathlib
import Definitions.Def_FowlerLSQC_Shor_binaryLength
import Definitions.Def_FowlerLSQC_Shor_period

namespace FowlerLSQC.Shor

/-- Useful outcomes of quantum period finding yield `c/r` as a convergent (corrected:
`N₁ ≠ N₂`), Fowler, *Towards Large-Scale Quantum Computation*, arXiv:quant-ph/0506126v1, Ch. 7,
p.81 (PDF 99), in the setting of p.75 (PDF 93). Let `N = N₁N₂` with `N₁ ≠ N₂` primes, `L` the
binary length of `N`, `1 < m < N` with `gcd(m, N) = 1`, and `r` the period of `m^k mod N`. For
every `0 < c < r` and every `j = ⌊c·2^{2L}/r⌋` or `j = ⌈c·2^{2L}/r⌉` (a "useful" `j`), the
fraction `c/r` in lowest terms is a convergent of the continued fraction expansion of `j/2^{2L}`;
in particular its denominator `r / gcd(c, r)` is a divisor of `r`.

**Formalization Note** The `n`-th convergent is Mathlib's `Real.convergent`, whose index `0` is
`⌊j/2^{2L}⌋`, one before the book's first convergent (7.9); the existential over `n` is unaffected.
`(c : ℚ) / r` is automatically in lowest terms. `⌊·⌋`, `⌈·⌉` are `Nat.floor`, `Nat.ceil` of the
rational `c·2^{2L}/r`. The book allows `N₁ = N₂`; the statement is false then (N = 121, m = 2,
r = 110, L = 7, c = 17, j = 2533), and `N₁ ≠ N₂` is the correction. Oddness of `N` is not
assumed (the book assumes it only for its 0.75 claim). -/
theorem useful_convergent (N₁ N₂ N m c j : ℕ) (hN₁ : N₁.Prime) (hN₂ : N₂.Prime) (hne : N₁ ≠ N₂)
    (hN : N = N₁ * N₂) (hm1 : 1 < m) (hmN : m < N) (hcop : Nat.Coprime m N)
    (hc0 : 0 < c) (hcr : c < period N m)
    (hj : j = ⌊((c * 2 ^ (2 * binaryLength N) : ℕ) : ℚ) / (period N m : ℚ)⌋₊ ∨
      j = ⌈((c * 2 ^ (2 * binaryLength N) : ℕ) : ℚ) / (period N m : ℚ)⌉₊) :
    ∃ n : ℕ, ((j : ℝ) / 2 ^ (2 * binaryLength N)).convergent n = (c : ℚ) / (period N m : ℚ) := by sorry

end FowlerLSQC.Shor
