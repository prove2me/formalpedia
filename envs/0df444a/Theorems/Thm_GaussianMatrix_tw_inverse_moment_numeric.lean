-- Prove2me | Theorems.Thm_GaussianMatrix_tw_inverse_moment_numeric
-- name    : GaussianMatrix.tw_inverse_moment_numeric
-- status  : Proved
-- author  : @tc
-- created : 2026-10-09T06:42:55.763554+00:00
-- url     : https://prove2.me/theorems/4473d4c8-5cf9-45dc-9af2-826664c549c0
-- title:
--   Tropp–Webber numerical inequality (B.8): $\big(1+\frac{2p}{x+1-2p}\big)\Gamma(x+2)^{-2p/(x+1)}\le (e/x)^{2p}$ for $1\le p\le 18$, $x\ge 2p$
-- statement:
--   Let $p$ and $x$ be natural numbers with $1\le p\le 18$ and $x\ge 2p$. Then
--   $$\Big(1+\frac{2p}{x+1-2p}\Big)\Big(\frac{1}{\Gamma(x+2)}\Big)^{2p/(x+1)}\;\le\;\Big(\frac{e}{x}\Big)^{2p}.$$
--
--   Write $n=x+1$ and $c=2p$. The inequality is equivalent to $(1-c/n)^{-n/c}\,(n-1)^n\le e^n\,n!$. It follows from Stirling's lower bound $n!\ge\sqrt{2\pi n}\,(n/e)^n$, the bound $(1-1/n)^n\le e^{-1}$, and the concavity of $\log$, which gives $n\log\frac{n}{n-c}\le(c+1)\log(c+1)$ for $n\ge c+1$. What remains is the integer check $(2p+1)^{2p+2}\le 46^{2p}\le(2\pi e^2)^{2p}$, which holds exactly for $p\le 18$. This is the last step of the inverse-moment bound $\mathbb E\|(GG^\top)^{-1}\|^p\le\big(e^2(k+r)/(2(k-r)^2)\big)^p$, applied with $x=k-r$.
--
--   **Formalization Note.** $\Gamma$ is `Real.Gamma`. The exponent $2p/(x+1)$ is a real power and $(e/x)^{2p}$ is a natural power. The source states the inequality for real $0\le p\le18$ and real $x\ge 2p$; here it is specialised to integers $p\ge1$ and $x$, which is the case used.
-- source:
--   J. A. Tropp and R. J. Webber, Randomized algorithms for low-rank matrix approximation: design, analysis, and applications, arXiv:2306.12418, Appendix B, proof of Lemma B.3, inequality (B.8) (with the argument (B.9) and Stirling's approximation, Abramowitz–Stegun 6.1.38).

import Definitions.Def_GaussianMatrix_basic

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace GaussianMatrix

theorem tw_inverse_moment_numeric {p x : ℕ} (hp : 1 ≤ p) (hp18 : p ≤ 18) (hx : 2 * p ≤ x) :
    (1 + 2 * (p : ℝ) / ((x : ℝ) + 1 - 2 * p))
        * (1 / Real.Gamma ((x : ℝ) + 2)) ^ (2 * (p : ℝ) / ((x : ℝ) + 1))
      ≤ (Real.exp 1 / x) ^ (2 * p) := by sorry

end GaussianMatrix
