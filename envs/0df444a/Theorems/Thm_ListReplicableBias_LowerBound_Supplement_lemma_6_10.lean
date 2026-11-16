-- Prove2me | Theorems.Thm_ListReplicableBias_LowerBound_Supplement_lemma_6_10
-- name    : ListReplicableBias.LowerBound.Supplement.lemma_6_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:27:34.67109+00:00
-- url     : https://prove2.me/theorems/9f86b17b-e3ab-4233-9f50-5cc6566f9605
-- title:
--   Lemma 6.10 — the good-shift and accuracy events fail with probability at most 1/8 and η
-- statement:
--   Run Algorithm 1 with parameters $\varepsilon\in(0,1)$, $\eta\in(0,1/8)$ on $d\ge1$ coins with biases $p\in[0,1]^d$, and let
--   $$G=\bigcap_{i\in[d]}\{U\text{ is }3\alpha_m\text{-good for }p_i\},\qquad H=\bigcap_{i\in[d],\,j\in[m]}\{\hat p_i^{(j)}\in[p_i-\alpha_j,p_i+\alpha_j]\}.$$
--   Then
--   1. $\Pr(G^c)\le 1/8$;
--   2. $\Pr(H^c)\le\eta$;
--   3. $\Pr(G^c\cup H^c)\le 1/8+\eta\le1/4$.
--
--   On $G\cap H$ Algorithm 1 outputs the rounding $R_U(p)$ (Lemma 6.11), so these bounds control its failure probability.
--
--   Differences from the source:
--   - encoding: Algorithm 1 run on d coins with shift U ~ Unif([0, ε)), probabilities over U and the tosses → the explicit outcome space (U, all block tosses) with law Unif([0, ε)) ⊗ independent Bern(p_i) tosses; rounds 1..m are blocks Fin m (block b is round b+1); probabilities are ℝ≥0∞ masses; reason: this is the paper's own analysis model on PDF p. 10 (an independent block of n_j tosses for every coin and round, only used blocks counted)
--   - encoding: d ∈ ℕ coins indexed by [d] → 1 ≤ d; reason: at d = 0 the parameter m = ⌈log₂(24d)⌉ (and log(d/·)) is undefined, so only undefined cases are excluded
-- source:
--   Chen, Bastan, Pavan, Vinodchandran, The Price of List Replicability: Tight Bounds for Bias Estimation, STOC 2027 submission #681 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/681.pdf, Events G, H and Lemma 6.10, PDF p. 10

import Mathlib
import Definitions.Def_ListReplicableBias_LowerBound_Geometry
import Definitions.Def_ListReplicableBias_LowerBound_Supplement_Algorithms

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ListReplicableBias.LowerBound.Supplement

open ListReplicableBias.LowerBound

/-- Lemma 6.10, PDF p. 10, all three clauses (both inequalities of (3)). -/
theorem lemma_6_10 (d : ℕ) (hd : 1 ≤ d) (ε η : ℝ) (hε : ε ∈ Set.Ioo (0 : ℝ) 1)
    (hη : η ∈ Set.Ioo (0 : ℝ) (1 / 8)) (p : Fin d → ℝ) (hp : p ∈ cube d 0 1) :
    alg1Law d ε η p (eventG d ε η p)ᶜ ≤ ENNReal.ofReal (1 / 8) ∧
    alg1Law d ε η p (eventH d ε η p)ᶜ ≤ ENNReal.ofReal η ∧
    alg1Law d ε η p ((eventG d ε η p)ᶜ ∪ (eventH d ε η p)ᶜ) ≤ ENNReal.ofReal (1 / 8 + η) ∧
    1 / 8 + η ≤ 1 / 4 := by sorry

end ListReplicableBias.LowerBound.Supplement
