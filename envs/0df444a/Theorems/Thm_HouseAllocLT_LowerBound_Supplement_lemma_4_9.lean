-- Prove2me | Theorems.Thm_HouseAllocLT_LowerBound_Supplement_lemma_4_9
-- name    : HouseAllocLT.LowerBound.Supplement.lemma_4_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T14:20:37.287887+00:00
-- url     : https://prove2.me/theorems/723a2951-aaad-4c65-bc4f-5f773263d225
-- title:
--   Lemma 4.9 — bounds on λₙ and integer rounding
-- statement:
--   Let $n\ge1$ and $c=1-e^{-1}$, with $D_n=(n+2)!$ and $\lambda_n$ from (9). Then
--   $$c+\frac1{D_n}<\lambda_n\le1,$$
--   and for all integers $k,r$ with $1\le r\le n$,
--   $$\frac{k}{n!}\ge cr\ \Longrightarrow\ \frac{k}{n!}\ge r\lambda_n.$$
--
--   The rounding step converts the asymptotic constant $c$ into the finite-market constant $\lambda_n$ in Lemma 4.10 and (15).
--
--   Differences from the source: none.
-- source:
--   Jinshan Zhang, Nan Zhao, Hao Xu, Meng Xi, Lin Zhao, STOC 2027 submission #174 (October 2026), Lemma 4.9, PDF p. 13 (printed p. 11); constants (9), PDF p. 10 (printed p. 8); proof PDF pp. 20–21 (printed pp. 18–19); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/174.pdf

import Definitions.Def_HouseAllocLT_LowerBound_Supplement_LTRPG

open scoped BigOperators ENNReal
open Classical

namespace HouseAllocLT.LowerBound.Supplement
open HouseAllocLT.LowerBound

/-- Lemma 4.9, PDF p. 13 (printed p. 11). With `c = 1 − e^{−1}`: `c + 1/D_n < λ_n ≤ 1`, and for
integers `k, r` with `1 ≤ r ≤ n`, `k/n! ≥ c r` implies `k/n! ≥ r λ_n`. -/
theorem lemma_4_9 (n : ℕ) (hn : 1 ≤ n) :
    (1 - Real.exp (-1)) + 1 / (resDenom n : ℝ) < lambdaN n ∧ lambdaN n ≤ 1 ∧
    ∀ (k r : ℤ), 1 ≤ r → r ≤ n →
      (1 - Real.exp (-1)) * (r : ℝ) ≤ (k : ℝ) / (n.factorial : ℝ) →
        (r : ℝ) * lambdaN n ≤ (k : ℝ) / (n.factorial : ℝ) := by sorry

end HouseAllocLT.LowerBound.Supplement
