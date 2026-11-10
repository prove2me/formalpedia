-- Prove2me | Theorems.Thm_GEPPGrowth_Main_proposition_4_15
-- name    : GEPPGrowth.Main.proposition_4_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T23:38:10.320764+00:00
-- url     : https://prove2.me/theorems/1c5a0f31-2471-4c2b-b875-587939ed73b3
-- title:
--   Proposition 4.15 — Determinant lower tail
-- statement:
--   The probability is under the explicit covariance process initialized at identity; $\log$ denotes the natural logarithm.
--
--   Fix $2\le k\le n$. Let $d:=n-k+1$, and $\Sigma^{(k)}$ be
--   obtained from the covariance update process started at $\Sigma^{(1)}=I_n$. Then, for every $t>0$,
--
--   $$
--   \Pr(\det(\Sigma^{(k)})\le t)\le\left(\dfrac{t(d+2\log(n))^d}{n^{d(1-1/\lceil\log(n)\rceil)}}\right)^{\lceil\log(n)\rceil}
--   $$.
--
--   In particular,
--
--   $$
--   \Pr\left(\det(\Sigma^{(k)})\le\dfrac1e\left(\dfrac{n}{e(d+2\log(n))}\right)^d\right)\le\dfrac1n
--   $$.
--
--   This controls small determinants, including the explicit failure probability.
--
--   Differences from the source:
--   - encoding: source step k and covariance Σ^(k) → time k-1 with a zero-padded state and active leading block of dimension n-(k-1); reason: the leading block has exactly the source dimension n-k+1, with the explicit Gaussian transition law
-- source:
--   Daniel Spielman, Xifan Yu, STOC 2027 submission #1176 (October 2026), Proposition 4.15, printed p.13, PDF p.14

import Definitions.Def_GEPPGrowth_Main_Process
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix

noncomputable section

namespace GEPPGrowth.Main

/-- Proposition 4.15, printed p.13 / PDF p.14. Ceiling of the natural logarithm, with its real reciprocal inside the exponent. -/
theorem proposition_4_15 (n k : ℕ) (hk : 2 ≤ k) (hkn : k ≤ n) :
    (∀ t : ℝ, 0 < t →
      prob (covLaw n (k-1)) {S | (block S (n-(k-1))).det ≤ t} ≤
        (t * ((n-k+1:ℕ)+2*Real.log n)^ (n-k+1) /
          Real.rpow (n:ℝ) ((n-k+1:ℕ)*(1-1/(Nat.ceil (Real.log n):ℝ)))) ^
            Nat.ceil (Real.log n)) ∧
    prob (covLaw n (k-1)) {S | (block S (n-(k-1))).det ≤
      (1 / Real.exp 1) * ((n:ℝ) /
        (Real.exp 1 * ((n-k+1:ℕ)+2*Real.log n)))^(n-k+1)} ≤ 1/(n:ℝ) := by sorry

end GEPPGrowth.Main
