-- Prove2me | Theorems.Thm_LowRankIncoherent_Adaptive_proposition_3_21
-- name    : LowRankIncoherent.Adaptive.proposition_3_21
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T13:19:27.236202+00:00
-- url     : https://prove2.me/theorems/a2039fb6-66ca-4ec1-bc52-b45016e40058
-- title:
--   Proposition 3.21 — input selection from multiplicative estimates
-- statement:
--   In the standing feasible dimensions fix $s>0$ and a rank-at-most-$r$ channel. Put $T=\max\{1,\lceil\log_2a\rceil\}$ and $ρ_1=I_a/a$. Suppose the positive definite matrices $A_j$ satisfy $\tfrac34A(ρ_j)\preceq A_j\preceq\tfrac54A(ρ_j)$ for $j=1,\ldots,T$, and define
--   $$z_j=\operatorname{tr}\exp(\log ρ_j+\log A_j),\qquadρ_{j+1}=\exp(\log ρ_j+\log A_j)/z_j.$$
--   Then $\barρ=T^{-1}\sum_{j=1}^Tρ_j$ satisfies both equivalent conclusions
--   $$A(\barρ)\preceq10rI_a,\qquad H_s(σ(\barρ))\preceq9rI_a.$$
--   The estimates are hypotheses of this deterministic source proposition, not hypotheses of Algorithm 3's probabilistic goal. The two displayed conclusions and their equivalence are retained.
--
--   Differences from the source:
--   - encoding: rounds j=1,...,T and the recursively defined states → Fin T indices 0,...,T-1, starting from ρ 0, with the same update and average; reason: a shift of labels preserves all rounds, the final update, and both conclusions
-- source:
--   Aadil Oufkir, Kean Chen, STOC 2027 submission #364 (October 2026), Proposition 3.21, printed p. 33 = PDF p. 33; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/364.pdf

import Definitions.Def_LowRankIncoherent_Adaptive_Algorithm

open Matrix MeasureTheory
open scoped MatrixOrder ComplexOrder ENNReal
noncomputable section

namespace LowRankIncoherent.Adaptive

theorem proposition_3_21 {a b r : ℕ} (ha : 0 < a) (hb : 2 ≤ b) (hrpos : 1 ≤ r)
    (hrmax : r ≤ a*b) (hfeasible : a ≤ r*b)
    (E : Map a b) (hE : E ∈ ChanTomoNB.QChan r a b) (s : ℝ) (hs : 0 < s)
    (A : Fin (rounds a) → Input a) (ρ : ℕ → Input a)
    (hinit : ρ 0 = (1/(a : ℂ)) • 1)
    (hpd : ∀ j, (A j).PosDef)
    (hest : ∀ j : Fin (rounds a), LE ((3/4 : ℂ) • Amap E r s (ρ j)) (A j) ∧
      LE (A j) ((5/4 : ℂ) • Amap E r s (ρ j)))
    (hupdate : ∀ j : Fin (rounds a), ρ (j.val+1) = update (ρ j) (A j)) :
    let avg := (1/(rounds a : ℂ)) • ∑ j : Fin (rounds a), ρ j
    LE (Amap E r s avg) ((10*r : ℕ) • (1 : Input a)) ∧
    LE (sensitivity E s (mixture avg)) ((9*r : ℕ) • (1 : Input a)) ∧
    (LE (Amap E r s avg) ((10*r : ℕ) • (1 : Input a)) ↔
     LE (sensitivity E s (mixture avg)) ((9*r : ℕ) • (1 : Input a))) := by sorry

end LowRankIncoherent.Adaptive
