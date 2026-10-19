-- Prove2me | Theorems.Thm_MatchCongestion_Welfare_theorem_2
-- name    : MatchCongestion.Welfare.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T17:24:45.808231+00:00
-- url     : https://prove2.me/theorems/b79410bf-70c6-4d3d-aa4e-6c48404ab863
-- title:
--   Theorem 2, p. 628 — unique roots p̂, p̄ > c_a of (13), (14); in the unique MFE p∗ = min(p̂, p̄), with welfare (15), (16)
-- statement:
--   Let $r>0$ (applicants per employer), $0<\beta\le1$ (compatibility probability), $c_a>0$ (application cost) and $c_s>0$ (screening cost) satisfy Assumption 1, $\max(c_a,c_s)<\beta$. Then:
--
--   1. there is exactly one $\hat p>c_a$ solving
--   $$r\Bigl(1-\frac{c_a}{\hat p}\Bigr) = 1 - e^{-\frac{r\beta}{\hat p}\left(1-\frac{c_a}{\hat p}\right)}, \tag{13}$$
--   2. there is exactly one $\bar p>c_a$ solving
--   $$1-\frac{c_a}{\bar p} + \frac{c_s}{\beta}\log\Bigl(\frac{c_a}{\bar p}\Bigr) = 0, \tag{14}$$
--   3. there is exactly one mean-field equilibrium $(m^*,\alpha^*)$;
--   4. in it, the acceptance probability is $p^* = \min(\hat p,\bar p)$, and applicant and employer welfare are
--   $$\Pi^*_a = 1-\frac{c_a}{p^*}+\frac{c_a}{p^*}\log\Bigl(\frac{c_a}{p^*}\Bigr), \tag{15}$$
--   $$\Pi^*_e = r\Bigl(1-\frac{c_a}{p^*}+\frac{c_s}{\beta}\log\Bigl(\frac{c_a}{p^*}\Bigr)\Bigr). \tag{16}$$
--
--   Here a mean-field equilibrium is a pair $(m^*,\alpha^*)$ with a steady state $(p^*,q^*)$, $q^*=E(m^*p^*)$ and $p^*=\alpha^*\beta E(rm^*\beta q^*)$ with $E(x)=(1-e^{-x})/x$, $E(0)=1$, such that $m^*$ is the applicant best response (3) to $p^*$ and $\alpha^*$ lies in the employer best-response correspondence (4) at $q^*$; the welfares are $\Pi^*_a = W_a(m^*,p^*)$ and $\Pi^*_e = W_e(\alpha^*,m^*,q^*)$ from (2), (5), (10)–(12).
--
--   The theorem expresses equilibrium welfare through model primitives and a single scalar $p^*$. It splits markets into application-limited ($p^*=\hat p$, all employers screen) and screening-limited ($p^*=\bar p$, employers indifferent) regimes, which drive the paper's welfare comparisons and application-limit interventions.
--
--   **Formalization Note.** Item 4 is stated for every equilibrium together with any steady state witnessing it, and for any roots $\hat p,\bar p>c_a$ of (13), (14); items 1–3 make these unique, so the statement is not vacuous. The positivity of $r,\beta,c_a,c_s$ and $\beta\le 1$ are added to Assumption 1; $E(0)=1$ is the continuous extension of the ratio in (6)–(7); $\log$ is the natural logarithm.
-- source:
--   Arnosti, Johari, Kanoria, Managing Congestion in Matching Markets, M&SOM 23(3):620–636 (2021), p. 628, Theorem 2

import Mathlib
import Definitions.Def_MatchCongestion_Welfare_Setting

namespace MatchCongestion.Welfare

/-- Arnosti, Johari, Kanoria, *Managing Congestion in Matching Markets*, M&SOM 23(3):620–636 (2021),
p. 628, Theorem 2: there are unique solutions `p̂, p̄ > c_a` to
(13) `r (1 - c_a/p̂) = 1 - e^{-(rβ/p̂)(1 - c_a/p̂)}` and (14) `1 - c_a/p̄ + (c_s/β) log(c_a/p̄) = 0`.
In the unique MFE, `p* = min(p̂, p̄)`, and
(15) `Π*_a = 1 - c_a/p* + (c_a/p*) log(c_a/p*)`,
(16) `Π*_e = r (1 - c_a/p* + (c_s/β) log(c_a/p*))`.

**Formalization Note.**
* "The unique MFE" is the conjunct `∃! (m, α), IsMFE` (Theorem 1); the remaining clause is stated for
  every MFE with its steady state `(p, q)`, so it is not vacuous.
* `p̂`, `p̄` are quantified (any roots `> c_a` of (13), (14)), not chosen.
* `p* = P(m*, α*)` and `q* = Q(m*, α*)` are the MFE's steady state; by (10)–(12)
  `Π*_a = W_a(m*, p*)` and `Π*_e = W_e(α*, m*, q*)`.
* `Standing` = Assumption 1 plus `0 < r`, `0 < β ≤ 1`, `0 < c_a`, `0 < c_s`; (6)–(7) use `E 0 = 1`;
  `log` is `Real.log`. -/
theorem theorem_2 (P : Params) (hP : P.Standing) :
    (∃! p : ℝ, P.ca < p ∧ Eq13 P p) ∧
    (∃! p : ℝ, P.ca < p ∧ Eq14 P p) ∧
    (∃! mα : ℝ × ℝ, IsMFE P mα.1 mα.2) ∧
    ∀ ph pb : ℝ, P.ca < ph → Eq13 P ph → P.ca < pb → Eq14 P pb →
      ∀ m α p q : ℝ, IsMFSS P m α p q → m = Mbr P p → α ∈ Acorr P q →
        p = min ph pb ∧
        Wa P m p = 1 - P.ca / p + P.ca / p * Real.log (P.ca / p) ∧
        We P α m q = P.r * (1 - P.ca / p + P.cs / P.β * Real.log (P.ca / p)) := by sorry

end MatchCongestion.Welfare
