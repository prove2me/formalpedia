-- Prove2me | Theorems.Thm_IIDMultiItem_TwoPoint_section_B_4
-- name    : IIDMultiItem.TwoPoint.section_B_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T20:57:30.29239+00:00
-- url     : https://prove2.me/theorems/6038e9ce-6542-4efc-a725-b07e8cb86d80
-- title:
--   §B.4, (B.2)–(B.3) — the value (3.6) as a finite sum over (c, r), and the generating-function formula for ϖ_{c,r}
-- statement:
--   Let $n,m\ge1$, $0<a<b$, $0<p<1$, $q=1-p$, and $\varpi_{c,r}=\Pr[|L|=c,\ e^*=r]$ for profiles $S_1,\dots,S_n$ i.i.d. with $\Pr[S_i=A]=p^{m-|A|}q^{|A|}$. Then
--   $$mb(1-p^n)+\mathbb E_S\big[c\,[\phi_{c,e^*}]_+\big]=mb(1-p^n)+\sum_{c=1}^m\sum_{r=0}^{m-c}c\,\varpi_{c,r}\,[\phi_{c,r}]_+.\tag{B.2}$$
--   With $\pi_0=p^n$, $\pi_1=qp^{n-1}$, $\pi_2=1-p^n-nqp^{n-1}$, a formal variable $w$, $[w^k]$ the coefficient of $w^k$, $E_r(w)=\sum_{k=0}^r(\pi_1w)^k/k!$, $E_{-1}=0$, $G(w)=\sum_{c_2=0}^m(\pi_2w)^{c_2}/c_2!$ and $0^0=1$: for all $0\le c\le m$ and $r\ge0$,
--   $$\varpi_{c,r}=\frac{m!\,\pi_0^c}{c!}\,[w^{m-c}]\,G(w)\big(E_r(w)^n-E_{r-1}(w)^n\big).\tag{B.3}$$
--
--   Together these reduce (3.6) to polynomially many rational terms, which is the basis of the value clause of Theorem 3.3.
--
--   Differences from the source:
--   - reading: (B.2) with left side OPT(F; n, m), introduced by 'By (3.6)' → left side revFormula a b p n m, the expression (3.6); reason: (B.2) rewrites the expression (3.6); its equality with OPT is the goal theorem, not part of this step
--   - encoding: (B.3) for the pairs (c, r) used in (B.2) → for every c ≤ m and every r ≥ 0; reason: (B.3) as displayed is stated for every such pair; the derivation covers them all
--   - encoding: [w^k] of polynomials, E_r, E_{−1} = 0, G → Polynomial.coeff over ℝ, expTrunc π_1 (r + 1), expTrunc π_1 0 = 0, expTrunc π_2 (m + 1); reason: the same polynomials; Lean's 0^0 = 1 is the paper's convention
-- source:
--   Liu, Liu, Wang, Optimal Multi-Item Auctions with I.I.D. Values, arXiv:2610.11051 (held version, PDF of 2026-11-03, sha256 983080a4…), pp. 38–39 (PDF 40–41), §B.4, (B.2)–(B.3)

import Mathlib
import Definitions.Def_IIDMultiItem_TwoPoint_Counts

open scoped BigOperators

namespace IIDMultiItem.TwoPoint

/-- §B.4, (B.2)–(B.3). With `ϖ_{c,r} = Pr[|L| = c, e* = r]`,
`(3.6) = m b (1 − p^n) + ∑_{c=1}^m ∑_{r=0}^{m−c} c ϖ_{c,r} [ϕ_{c,r}]_+` (B.2), and, with
`π_0 = p^n`, `π_1 = q p^{n−1}`, `π_2 = 1 − p^n − n q p^{n−1}`, `E_r(w) = ∑_{k=0}^r (π_1 w)^k/k!`,
`E_{−1} = 0`, `G(w) = ∑_{c_2=0}^m (π_2 w)^{c_2}/c_2!`:
`ϖ_{c,r} = (m! π_0^c / c!) [w^{m−c}] G(w)(E_r(w)^n − E_{r−1}(w)^n)` (B.3). -/
theorem section_B_4 (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) (a b p : ℝ) (ha : 0 < a) (hab : a < b)
    (hp0 : 0 < p) (hp1 : p < 1) :
    revFormula a b p n m =
      m * b * (1 - p ^ n) +
        ∑ c ∈ Finset.Icc 1 m, ∑ r ∈ Finset.range (m - c + 1),
          (c : ℝ) * lowMaxProb p n m c r * max (phi a b p c r) 0 ∧
    ∀ c r : ℕ, c ≤ m →
      lowMaxProb p n m c r =
        ((m.factorial : ℝ) * (p ^ n) ^ c / (c.factorial : ℝ)) *
          (expTrunc (1 - p ^ n - n * (1 - p) * p ^ (n - 1)) (m + 1) *
            (expTrunc ((1 - p) * p ^ (n - 1)) (r + 1) ^ n -
              expTrunc ((1 - p) * p ^ (n - 1)) r ^ n)).coeff (m - c) := by sorry

end IIDMultiItem.TwoPoint
