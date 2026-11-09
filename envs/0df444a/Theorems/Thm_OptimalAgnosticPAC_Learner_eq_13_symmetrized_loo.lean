-- Prove2me | Theorems.Thm_OptimalAgnosticPAC_Learner_eq_13_symmetrized_loo
-- name    : OptimalAgnosticPAC.Learner.eq_13_symmetrized_loo
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:58:37.370903+00:00
-- url     : https://prove2.me/theorems/8356ba7c-d990-4a50-bdf2-af9ab489097f
-- title:
--   Equation (13): the symmetrized leave-one-out score
-- statement:
--   Let $\mathcal H$ be a nonempty class of measurable classifiers with $\mathrm{VC}(\mathcal H)\le d$, $d\ge1$, and suppose its traces depend measurably on the points. There is a score family $q(\cdot;S)$, defined for samples $S$ of every length, such that:
--
--   1. $q(x;S)\in[-1,1]$;
--   2. $q$ is symmetric in the observations of $S$;
--   3. $(S,x)\mapsto q(x;S)$ is measurable;
--   4. for every sample $S=((x_i,y_i))_{i=1}^m$ with $m\ge1$,
--   $$\frac1{2m}\sum_{i=1}^m|q(x_i;S^{-i})-y_i|\le\widehat L^*_S+120\sqrt{\frac{d\widehat L^*_S}{m}}+7202\frac dm.\tag{13}$$
--
--   In the paper, $q$ is the symmetrization of the leave-one-out rule of Theorem 2, and these are the properties on which §3 relies.
--
--   Differences from the source:
--   - encoding: labels in {−1,+1}, inputs in a set X → labels in Bool with true for +1, signed values through sgn, X : Type; reason: the reused vcDim takes Bool-valued functions on a Type; renaming the two labels changes no quantity
--   - reading: q(x; S) is the expected prediction of the rule of Theorem 2 over a uniform permutation → existence of a family with the four properties; reason: §3 uses only these properties, and the paper's q is such a family
--   - reading: footnote 1: all maps depending on the data are measurable → hypotheses that each h ∈ H is measurable and TraceMeasurable H; joint measurability of q is a conclusion; reason: q is existential, so assuming its measurability would be vacuous; a condition on H makes every trace-based rule measurable
--   - encoding: samples of size m ≥ 1 and S^{−i} → S : Fin (m + 1) → X × Bool with deleteObs S i, for m ≥ 0; reason: every length at least one, once each
--   - generalization: VC(H) = d ≥ 1 → H nonempty with vcDim H ≤ d, d ≥ 1; reason: the bound is increasing in d, so d = VC(H) gives the source's statement
-- source:
--   Dahl, Qian and Zhivotovskiy, An Optimal Agnostic PAC Algorithm, August 6, 2026 preprint, STOC 2027 submission #67, SHA-256 b61bab4e8b832787499a381cc9efadcf919f9384a3bcfae6c3412fb3e557e2fc, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/67.pdf, §3.1, equation (13), PDF p. 9 (printed p. 8)

import Mathlib
import Definitions.Def_HighDimProb_Chaining_VcDim
import Definitions.Def_OptimalAgnosticPAC_Learner_Score
open MeasureTheory
open scoped Classical

namespace OptimalAgnosticPAC.Learner

/-- Equation (13), PDF p. 9: there is a score family that is `[-1,1]`-valued, symmetric in the
observations, jointly measurable and satisfies (13) for every sample. -/
theorem eq_13_symmetrized_loo {X : Type} [MeasurableSpace X] (H : Set (X → Bool))
    (hH : H.Nonempty) (d : ℕ) (hd : 1 ≤ d)
    (hVC : HighDimProb.Chaining.vcDim H ≤ (d : ℕ∞))
    (hmeas : ∀ h ∈ H, Measurable h) (htrace : TraceMeasurable H) :
    ∃ q : (m : ℕ) → (Fin m → X × Bool) → X → ℝ, IsLOOScore H d q := by sorry

end OptimalAgnosticPAC.Learner
