-- Prove2me | Theorems.Thm_IndependentInfoPricing_Main_diagonal_ratio_diverges
-- name    : IndependentInfoPricing.Main.diagonal_ratio_diverges
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:33:44.901099+00:00
-- url     : https://prove2.me/theorems/c0f914a7-96f0-423a-bb0c-8fe1cd1dc9c0
-- title:
--   Proposition 3.5 — Diverging diagonal ratio
-- statement:
--   There are absolute constants $c>0$ and an integer $k_{\min}\ge2$ such that for each integer $k\ge k_{\min}$ there exists an integer $N(k)$ for which every $n\ge N(k)$ satisfies the probability-mass lower-bound condition and
--
--   $$\frac{\operatorname{Diag}(k,n)}{a(k)}\ge c\log\log a(k).$$
--
--   The family is the one actually defined in Section 3, with $a=e^k$ and $r=1+1/k$. The threshold for $n$ is selected after fixing $k$; the constant $c$ is independent of both. This is the quantified meaning of the source's asymptotic lower bound, not an assumption of diverging optimal ratios.
--
--   Differences from the source:
--   - encoding: Diag/a = Omega(log log a) for n sufficiently large after choosing a → there exist c>0 and kmin>=2 such that for all k>=kmin there exists N(k) and for all n>=N(k) the explicit family obeys the bound; reason: spells out the source Riemann-sum quantifier order and the probability-mass parameter restriction without changing its asymptotic assertion
-- source:
--   Hu Fu, Chenshuo Guo, STOC 2027 submission #1459 (October 2026), Proposition 3.5, printed pp.18–18 (PDF pp.20–20); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1459.pdf

import Definitions.Def_IndependentInfoPricing_Main_Diagonal

open MeasureTheory
open scoped BigOperators ENNReal
noncomputable section

namespace IndependentInfoPricing.Main

/-- Proposition 3.5, pp.18–20 (PDF 20–22): n is chosen after k, uniformly beyond N(k). -/
theorem diagonal_ratio_diverges :
    ∃ c : ℝ, 0 < c ∧ ∃ kmin : ℕ, 2 ≤ kmin ∧
      ∀ k : ℕ, kmin ≤ k → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        FamilyParameters k n ∧ c * Real.log (Real.log (baseA k)) ≤ diagonalRevenue k n / baseA k := by sorry

end IndependentInfoPricing.Main
