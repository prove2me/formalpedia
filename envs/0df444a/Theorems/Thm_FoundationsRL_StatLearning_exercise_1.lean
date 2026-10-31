-- Prove2me | Theorems.Thm_FoundationsRL_StatLearning_exercise_1
-- name    : FoundationsRL.StatLearning.exercise_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:19:29.348995+00:00
-- url     : https://prove2.me/theorems/84978d56-df6f-428e-a369-70f0a1d682a9
-- title:
--   Exercise 1 (1.38) — Proposition 1, Part 2, in high probability
-- statement:
--   Let the data be i.i.d., $\mathcal F$ a finite class of measurable functions $\mathcal X\to[0,1]$ with $f^\star\in\mathcal F$, and $Y_i\in[0,1]$ almost surely. There is an absolute constant $C>0$ such that for all $T\ge1$ and $\delta\in(0,1)$, with probability at least $1-\delta$, the empirical risk minimizer with respect to square loss satisfies
--
--   $$
--   \mathcal E(\widehat f)\le\frac{C\log(|\mathcal F|/\delta)}{T}.
--   $$
--
--   This is the high-probability form of the fast rate in Proposition 1.
--
--   Differences from the source:
--   - encoding: ≲ / an absolute constant → ∃ C > 0 quantified before all types and data; reason: the notes' meaning of an absolute constant
--   - encoding: measurability left implicit → members of the class are measurable (ℓ ∘ f measurable); reason: the field's standing convention; the expectations are undefined otherwise
--   - encoding: with probability at least 1 − δ, δ unconstrained → 0 < δ < 1; reason: the range stated at (1.12)
--   - encoding: f̂ ∈ argmin (1.6) → every measurable selection of the argmin; reason: the probability of the event is defined only for a measurable selection
--   - encoding: T not stated → T ≥ 1; reason: the sample mean and the bound divide by T
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, Exercise 1, (1.38), p. 19

import Mathlib
import Definitions.Def_FoundationsRL_StatLearning_excessLoss
import Definitions.Def_FoundationsRL_StatLearning_sqLoss
import Definitions.Def_FoundationsRL_StatLearning_dataLaw
import Definitions.Def_FoundationsRL_StatLearning_IsERM
import Definitions.Def_FoundationsRL_StatLearning_IsWellSpecified
open MeasureTheory
universe u

namespace FoundationsRL.StatLearning

/-- **Exercise 1** (Proposition 1, Part 2, high-probability form) (1.38). Let the data be i.i.d.,
`F = {f : X → [0, 1]}` finite, `f⋆ ∈ F`, and `Y_i ∈ [0, 1]` almost surely. Then with probability at
least `1 − δ`, the empirical risk minimizer with respect to square loss satisfies
`E(f̂) ≲ log(|F|/δ)/T`.
Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision Making*, arXiv:2312.16730v1, Exercise 1, (1.38), p. 19.

**Formalization Note.** `≲` is `∃ C > 0`, with `C` chosen before all types and data, so it is an
absolute constant. `δ ∈ (0, 1)` as at (1.12). Members of `F` are measurable, the field's standing
convention. -/
theorem exercise_1 : ∃ C : ℝ, 0 < C ∧
    ∀ (X : Type u) [MeasurableSpace X]
    (M : Measure (X × ℝ)) [IsProbabilityMeasure M]
    (F : Finset (X → ℝ)) (hF : F.Nonempty) (hmeas : ∀ f ∈ F, Measurable f)
    (hrange : ∀ f ∈ F, ∀ x, f x ∈ Set.Icc (0 : ℝ) 1)
    (hy : ∀ᵐ z ∂M, z.2 ∈ Set.Icc (0 : ℝ) 1)
    (_hspec : IsWellSpecified M F)
    (T : ℕ) (_hT : 0 < T) (fhat : (Fin T → X × ℝ) → X → ℝ) (_hfhat : IsERM sqLoss F fhat)
    (δ : ℝ) (_hδ0 : 0 < δ) (_hδ1 : δ < 1),
    1 - δ ≤ (dataLaw M T).real {D | excessLoss M sqLoss F hF (fhat D) ≤
      C * Real.log ((F.card : ℝ) / δ) / (T : ℝ)} := by sorry

end FoundationsRL.StatLearning
