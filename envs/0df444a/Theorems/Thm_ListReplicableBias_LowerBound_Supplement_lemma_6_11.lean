-- Prove2me | Theorems.Thm_ListReplicableBias_LowerBound_Supplement_lemma_6_11
-- name    : ListReplicableBias.LowerBound.Supplement.lemma_6_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:28:15.260551+00:00
-- url     : https://prove2.me/theorems/c7d8584b-db6e-474e-9132-f5e87f1cf5fe
-- title:
--   Lemma 6.11 — on H the output is R_U(p) or ⊥, and on G ∩ H it is R_U(p)
-- statement:
--   In the setting of Lemma 6.10 (Algorithm 1, $\varepsilon\in(0,1)$, $\eta\in(0,1/8)$, $d\ge1$, $p\in[0,1]^d$), with output $Y$:
--   1. on $H$, $Y\in\{R_U(p),\bot\}$; in particular $\Pr\big(Y\notin\mathcal L_p\cup\{\bot\}\big)\le\eta$;
--   2. on $G\cap H$, $Y=R_U(p)$; in particular $\Pr(Y=\bot)\le1/4$.
--
--   The first clause is the list-replicability of Algorithm 1 (its non-$\bot$ outputs fall in the canonical list), the second its success probability.
--
--   Differences from the source:
--   - encoding: Algorithm 1 run on d coins with shift U ~ Unif([0, ε)), probabilities over U and the tosses → the explicit outcome space (U, all block tosses) with law Unif([0, ε)) ⊗ independent Bern(p_i) tosses; rounds 1..m are blocks Fin m (block b is round b+1); probabilities are ℝ≥0∞ masses; reason: this is the paper's own analysis model on PDF p. 10 (an independent block of n_j tosses for every coin and round, only used blocks counted)
--   - encoding: d ∈ ℕ coins indexed by [d] → 1 ≤ d; reason: at d = 0 the parameter m = ⌈log₂(24d)⌉ (and log(d/·)) is undefined, so only undefined cases are excluded
--   - encoding: 'on H, Y ∈ {R_U(p), ⊥}' → for every outcome ω ∈ H, the output is some (R_U(p)) or none; reason: H is a set of outcomes of the block model
-- source:
--   Chen, Bastan, Pavan, Vinodchandran, The Price of List Replicability: Tight Bounds for Bias Estimation, STOC 2027 submission #681 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/681.pdf, Lemma 6.11, PDF pp. 10–11

import Mathlib
import Definitions.Def_ListReplicableBias_LowerBound_Geometry
import Definitions.Def_ListReplicableBias_LowerBound_Supplement_Algorithms

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ListReplicableBias.LowerBound.Supplement

open ListReplicableBias.LowerBound

/-- Lemma 6.11, PDF p. 10: both pointwise claims and both probability bounds. -/
theorem lemma_6_11 (d : ℕ) (hd : 1 ≤ d) (ε η : ℝ) (hε : ε ∈ Set.Ioo (0 : ℝ) 1)
    (hη : η ∈ Set.Ioo (0 : ℝ) (1 / 8)) (p : Fin d → ℝ) (hp : p ∈ cube d 0 1) :
    (∀ ω ∈ eventH d ε η p,
      alg1Output ω = some (roundVec ε ω.1 p) ∨ alg1Output ω = none) ∧
    alg1Law d ε η p {ω | alg1Output ω ∉ (some '' canonicalList ε p) ∪ {none}} ≤
      ENNReal.ofReal η ∧
    (∀ ω ∈ eventG d ε η p ∩ eventH d ε η p, alg1Output ω = some (roundVec ε ω.1 p)) ∧
    alg1Law d ε η p {ω | alg1Output ω = none} ≤ ENNReal.ofReal (1 / 4) := by sorry

end ListReplicableBias.LowerBound.Supplement
