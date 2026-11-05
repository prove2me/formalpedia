-- Prove2me | Theorems.Thm_FowlerLSQC_Shor_period_eq_lcm_den
-- name    : FowlerLSQC.Shor.period_eq_lcm_den
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:35:42.741287+00:00
-- url     : https://prove2.me/theorems/ec4e881c-f5ba-4561-ad20-b387582a6ea9
-- title:
--   Period as the lcm of two reduced denominators (corrected: coprime numerators of $c/r$, $c'/r$)
-- statement:
--   Let $r$ be a positive integer and let $c,c'$ be integers with $0<c<r$, $0<c'<r$ and $\gcd(c,c')=1$. Write $d=r/\gcd(c,r)$ and $d'=r/\gcd(c',r)$ for the denominators of $c/r$ and $c'/r$ in lowest terms. Then
--   $$
--   r=\operatorname{lcm}(d,d').
--   $$
--
--   In Shor's algorithm $c/r$ and $c'/r$ (in lowest terms) are convergents of two useful outcomes, so two runs whose underlying numerators are coprime recover the period as the least common multiple of the two convergent denominators.
--
--   **Formalization Note** The denominator of $c/r$ in lowest terms is the denominator of the rational number $c/r$.
--
--   Differences from the source:
--   - correction: "If a pair $c_{mn},c_{m'n'}$ exists such that $\gcd(c_{mn},c_{m'n'})=1$ and $d_{mn},d_{m'n'}$ are divisors of $r$ then $r=\operatorname{lcm}(d_{mn},d_{m'n'})$" (coprime convergent numerators) → coprime numerators $c,c'$ of $c/r$, $c'/r$ before reduction, with $d,d'$ the reduced denominators; reason: as printed it is false: $N=35$, $m=2$, $r=12$, $L=6$; $j=683=\lceil 2\cdot4096/12\rceil$ (useful, $c=2$) has the convergent $1/6$ and $j'=2048=6\cdot4096/12$ (useful, $c=6$) has the convergent $1/2$; the numerators $1,1$ are coprime and $6,2$ divide $12$, but $\operatorname{lcm}(6,2)=6\ne12$
--   - generalization: $r$ the period of $f(k)=m^k\bmod N$ → any positive integer $r$; reason: the identity is arithmetic in $r,c,c'$ and the period is a special case
-- source:
--   Fowler, Towards Large-Scale Quantum Computation, arXiv:quant-ph/0506126v1, Ch. 7, p.81 (PDF p.99)

import Mathlib

namespace FowlerLSQC.Shor

/-- Recovering the period as a least common multiple (corrected), Fowler, *Towards Large-Scale
Quantum Computation*, arXiv:quant-ph/0506126v1, Ch. 7, p.81 (PDF 99). The book: "If a pair
c_mn, c_m′n′ exists such that gcd(c_mn, c_m′n′) = 1 and d_mn, d_m′n′ are divisors of r then
r = lcm(d_mn, d_m′n′)". As printed (coprime convergent numerators) this is false; the corrected
statement asks for coprime `c, c′` in the useful outcomes `c/r`, `c′/r`, whose reduced
denominators `d = r / gcd(c, r)`, `d′ = r / gcd(c′, r)` are the convergent denominators the
procedure finds: for `0 < c, c′ < r` with `gcd(c, c′) = 1`, `r = lcm(d, d′)`.

**Formalization Note** The reduced denominator of `c/r` is `((c : ℚ) / r).den`. The statement is
for every `r`, not only the period of some `m^k mod N`. -/
theorem period_eq_lcm_den (r c c' : ℕ) (hc0 : 0 < c) (hcr : c < r) (hc'0 : 0 < c') (hc'r : c' < r)
    (hcop : Nat.Coprime c c') :
    Nat.lcm ((c : ℚ) / r).den ((c' : ℚ) / r).den = r := by sorry

end FowlerLSQC.Shor
