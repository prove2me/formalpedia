-- Prove2me | Theorems.Thm_GEPPGrowth_Main_proposition_5_3
-- name    : GEPPGrowth.Main.proposition_5_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T23:38:06.376712+00:00
-- url     : https://prove2.me/theorems/676f0fe3-3a5a-47d7-8733-d5d4bb414eb3
-- title:
--   Proposition 5.3 — Iterated covariance growth
-- statement:
--   The variables $T,d,r$ are integers. The initial matrix $S^{(0)}$ has dimension $d+1$, and the final matrix has dimension $T+1$. The case $r=0$ is included.
--
--   Fix $T\ge4$. Let $T\le d\le n-2$. Consider the covariance update process that
--   starts with $\Sigma^{(1)}=I_n$. Let $r:=d-T$ and $S^{(i)}:=\Sigma^{(n-d+i)}$ for $0\le i\le r$. Then,
--
--   $$
--   \Pr\left(\dfrac{\|S^{(r)}\|_2}{\max\{N_d,1\}}\ge\left(\dfrac32-\dfrac2T\right)^r\right)\ge\left(\dfrac12-\dfrac1n\right)\cdot\dfrac{0.16^{r(r+2T+3)/2}}{(32\sqrt2)^r(r+T+1)^{r(r+3)/4}n^{3r(r+T+2)/2}}
--   $$,
--
--   where we define
--
--   $$
--   N_d:=\dfrac{n}{e^{1+1/(d+1)}(d+1+2\log(n))}
--   $$.
--
--   This quantifies the complete iterated growth event with the source constants.
--
--   Differences from the source:
--   - encoding: source step k and covariance Σ^(k) → time k-1 with a zero-padded state and active leading block of dimension n-(k-1); reason: the leading block has exactly the source dimension n-k+1, with the explicit Gaussian transition law
-- source:
--   Daniel Spielman, Xifan Yu, STOC 2027 submission #1176 (October 2026), Proposition 5.3, printed p.18, PDF p.19

import Definitions.Def_GEPPGrowth_Main_Process
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix

noncomputable section

namespace GEPPGrowth.Main

/-- Proposition 5.3, printed p.18 / PDF p.19. Includes r=0; the final block has dimension T+1 and the initial block dimension d+1. -/
theorem proposition_5_3 (n T d : ℕ) (hT : 4 ≤ T) (hTd : T ≤ d) (hdn : d ≤ n-2) :
    let r := d-T
    (1/2 - 1/(n:ℝ)) *
      Real.rpow (0.16:ℝ) ((r:ℝ)*((r:ℝ)+2*T+3)/2) /
      ((32*Real.sqrt 2)^r * Real.rpow ((r:ℝ)+T+1) ((r:ℝ)*((r:ℝ)+3)/4) *
        Real.rpow (n:ℝ) (3*(r:ℝ)*((r:ℝ)+T+2)/2)) ≤
      prob (covLaw n (n-d+r-1)) {S |
        (3/2 - 2/(T:ℝ))^r ≤
          GaussianMatrix.specNorm (block S (n-(n-d+r-1))) / max (initialNormBound n d) 1} := by sorry

end GEPPGrowth.Main
