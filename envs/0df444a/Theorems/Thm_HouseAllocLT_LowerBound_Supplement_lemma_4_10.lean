-- Prove2me | Theorems.Thm_HouseAllocLT_LowerBound_Supplement_lemma_4_10
-- name    : HouseAllocLT.LowerBound.Supplement.lemma_4_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T14:21:13.887807+00:00
-- url     : https://prove2.me/theorems/f43bb96a-ac03-4aa6-8da5-763ae5b3560f
-- title:
--   Lemma 4.10 — RPG approximates every rank prefix within 1/λₙ
-- statement:
--   Let $n,m\ge1$ and fix a deterministic maximum-matching routine. For every profile $P$ (ties, incomplete and empty lists allowed) and every rank threshold $h$ with $R_h^*(P)>0$,
--   $$X_h^{\mathrm{RPG}}(P)\ge\lambda_nR_h^*(P),\qquad \alpha_{n,m}(\mathrm{RPG})\le\frac1{\lambda_n}<\frac e{e-1}.$$
--
--   This is the approximation half of Theorem 4.1.
--
--   Differences from the source:
--   - encoding: ranks and classes numbered from one → classes numbered from zero (paper rank j is class j−1); reason: a bijection of indices, no instance changes
--   - encoding: a fixed deterministic maximum-matching routine → a universally quantified routine `MM`; reason: the source states the result for whatever fixed routine RPG uses, which is the same claim
-- source:
--   Jinshan Zhang, Nan Zhao, Hao Xu, Meng Xi, Lin Zhao, STOC 2027 submission #174 (October 2026), Lemma 4.10, display (13), PDF p. 13 (printed p. 11); proof PDF p. 21 (printed p. 19); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/174.pdf

import Definitions.Def_HouseAllocLT_LowerBound_Supplement_LTRPG

open scoped BigOperators ENNReal
open Classical

namespace HouseAllocLT.LowerBound.Supplement
open HouseAllocLT.LowerBound

/-- Lemma 4.10, PDF p. 13 (printed p. 11). For every profile with `n` agents and `m` objects
(ties, incomplete and empty lists allowed) and every rank threshold `h` with `R*_h(P) > 0`,
`X_h^{RPG}(P) ≥ λ_n R*_h(P)`; and `α_{n,m}(RPG) ≤ 1/λ_n < e/(e − 1)`. -/
theorem lemma_4_10 {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) (MM : MaxMatchingRoutine n m) :
    (∀ (P : Profile n m) (h : ℕ), 0 < benchmarkPrefix P h →
      lambdaN n * (benchmarkPrefix P h : ℝ) ≤ expectedPrefix (rpg MM) P h) ∧
    approximationRatio (rpg MM) ≤ ENNReal.ofReal (1 / lambdaN n) ∧
    1 / lambdaN n < Real.exp 1 / (Real.exp 1 - 1) := by sorry

end HouseAllocLT.LowerBound.Supplement
