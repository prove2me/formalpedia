-- Prove2me | Theorems.Thm_GEPPGrowth_Main_proposition_4_14
-- name    : GEPPGrowth.Main.proposition_4_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T23:38:06.595979+00:00
-- url     : https://prove2.me/theorems/0b88dcb7-b136-42e3-9172-fccca7c91644
-- title:
--   Proposition 4.14 — Determinant upper tail
-- statement:
--   The probability is under the explicit covariance process initialized at identity, without conditioning on any favorable determinant event.
--
--   Fix $2\le k\le n$. Let $d:=n-k+1$, and $\Sigma^{(k)}$ be
--   obtained from the covariance update process started at $\Sigma^{(1)}=I_n$. Then, for every $t>0$,
--
--   $$
--   \Pr(\det(\Sigma^{(k)})\ge t)\le\dfrac{4n^{d+1}}{t^{1/3}}
--   $$
--
--   In particular,
--
--   $$
--   \Pr(\det(\Sigma^{(k)})\ge512n^{3d+3})\le\dfrac12
--   $$.
--
--   This controls large determinants and records the explicit half-probability threshold.
--
--   Differences from the source:
--   - encoding: source step k and covariance Σ^(k) → time k-1 with a zero-padded state and active leading block of dimension n-(k-1); reason: the leading block has exactly the source dimension n-k+1, with the explicit Gaussian transition law
-- source:
--   Daniel Spielman, Xifan Yu, STOC 2027 submission #1176 (October 2026), Proposition 4.14, printed p.11, PDF p.12

import Definitions.Def_GEPPGrowth_Main_Process
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix

noncomputable section

namespace GEPPGrowth.Main

/-- Proposition 4.14, printed p.11 / PDF p.12. Both the all-threshold bound and the explicit consequence are retained. -/
theorem proposition_4_14 (n k : ℕ) (hk : 2 ≤ k) (hkn : k ≤ n) :
    (∀ t : ℝ, 0 < t →
      prob (covLaw n (k-1)) {S | t ≤ (block S (n-(k-1))).det} ≤
        4 * (n:ℝ)^((n-k+1)+1) / Real.rpow t (1/3)) ∧
    prob (covLaw n (k-1)) {S | 512 * (n:ℝ)^(3*(n-k+1)+3) ≤
      (block S (n-(k-1))).det} ≤ 1/2 := by sorry

end GEPPGrowth.Main
