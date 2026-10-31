-- Prove2me | Theorems.Thm_FoundationsRL_StatLearning_proposition_1
-- name    : FoundationsRL.StatLearning.proposition_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:19:37.795093+00:00
-- url     : https://prove2.me/theorems/94a1e857-4519-46a6-86a6-3b8adfac7056
-- title:
--   Proposition 1, Parts 1–2: ERM over a finite class (corrected: range $[0,1]$ in Part 2; the "In addition" clause is the companion `proposition_1_improper`)
-- statement:
--   For any finite nonempty class $\mathcal F$ and $T\ge1$ i.i.d. examples, every empirical risk minimizer $\widehat f$ satisfies
--
--   $$
--   \mathbb E\big[\mathcal E(\widehat f)\big]\le C\cdot\mathrm{comp}(\mathcal F,T),
--   $$
--
--   with one absolute constant $C>0$, where:
--
--   1. For any bounded loss, with $\ell\circ f\in[a,b]$ almost surely for every $f\in\mathcal F$,
--   $$
--   \mathbb E\big[\mathcal E(\widehat f)\big]\le C\,(b-a)\sqrt{\frac{\log|\mathcal F|}{T}}.
--   $$
--   2. For square loss regression with $\mathcal F$ consisting of functions into $[0,1]$ and $y\in[0,1]$ almost surely, if the problem is well-specified,
--   $$
--   \mathbb E\big[\mathcal E(\widehat f)\big]\le\frac{C\log|\mathcal F|}{T}.
--   $$
--
--   Both rates depend on the class only through $\log|\mathcal F|$, not on the size of the feature space. The first is the slow rate, valid for generic losses, and the second is the fast rate, which uses the curvature of the square loss.
--
--   **Formalization Note** The theorem holds for every measurable selection of the argmin. For $|\mathcal F|=1$ both bounds are $0$, which is correct since the excess loss is then $0$.
--
--   Differences from the source:
--   - reading: "any bounded loss", with "the range of losses for the first part hidden" in ≲ (p. 9) → ℓ ∘ f ∈ [a, b] almost surely, with an explicit factor b − a and an absolute C; reason: the absolute constant must not depend on the range, and specializes to [0, 1] as in Lemma 4
--   - correction: F and y on Y = Y′ = ℝ, as at p. 7 → F takes values in [0, 1] and y ∈ [0, 1] almost surely, the setting of Exercise 1 (p. 19); reason: no absolute constant exists on ℝ. Counterexample: T = 1, X a point, y = c or 0 with probability 1/2 each, F = {c/2, 3c/4}; f⋆ = c/2 ∈ F, ERM picks 3c/4 when y = c, so E[E(f̂)] = c²/32 while log|F|/T = log 2
--   - encoding: ≲ / an absolute constant → ∃ C > 0 quantified before all types and data; reason: the notes' meaning of an absolute constant
--   - encoding: measurability left implicit → members of the class are measurable (ℓ ∘ f measurable); reason: the field's standing convention; the expectations are undefined otherwise
--   - encoding: f̂ ∈ argmin (1.6) → every measurable selection of the argmin; reason: the expectation of a non-measurable function is undefined
--   - encoding: T not stated → T ≥ 1; reason: comp(F, T) divides by T
--   - encoding: the closing "In addition" clause belongs to Proposition 1 → stated in the companion item FoundationsRL.StatLearning.proposition_1_improper, a milestone of this mission; reason: it concerns a different algorithm and its own quantifiers; the title of this item marks the split
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, Proposition 1, (1.9), p. 9

import Mathlib
import Definitions.Def_FoundationsRL_StatLearning_excessLoss
import Definitions.Def_FoundationsRL_StatLearning_sqLoss
import Definitions.Def_FoundationsRL_StatLearning_dataLaw
import Definitions.Def_FoundationsRL_StatLearning_IsERM
import Definitions.Def_FoundationsRL_StatLearning_IsWellSpecified
open MeasureTheory
universe u v w

namespace FoundationsRL.StatLearning

/-- **Proposition 1, Parts 1 and 2** (ERM over a finite class). For any finite class `F`, empirical
risk minimization satisfies `E[E(f̂)] ≲ comp(F, T)` (1.9), where
1. for any bounded loss, `comp(F, T) = √(log|F|/T)`;
2. for square loss regression, if the problem is well-specified, `comp(F, T) = log|F|/T`.
Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision Making*, arXiv:2312.16730v1, Proposition 1, (1.9), p. 9.
The closing "In addition" clause of the proposition, about a different algorithm, is the companion
`FoundationsRL.StatLearning.proposition_1_improper`.

**Formalization Note.** `≲` is `∃ C > 0`, with `C` chosen before every type, class, distribution,
loss and horizon. In Part 1 the range `[a, b]` of the loss appears as the factor `b − a`: the notes
say (p. 9) that the range is hidden in `≲`. In Part 2 the range is `[0, 1]`, the setting of Exercise 1
(p. 19) that proves this part: on `Y = ℝ` no absolute constant exists, because `y ↦ cy`, `f ↦ cf`
multiplies the excess square loss by `c²` and fixes `log|F|/T`. `fhat` is an arbitrary measurable
selection of the argmin (`IsERM`). -/
theorem proposition_1 : ∃ C : ℝ, 0 < C ∧
    (∀ (X : Type u) (Y : Type v) (Y' : Type w) [MeasurableSpace X] [MeasurableSpace Y]
      (M : Measure (X × Y)) [IsProbabilityMeasure M] (ℓ : Y' → Y → ℝ)
      (F : Finset (X → Y')) (hF : F.Nonempty)
      (_hmeas : ∀ f ∈ F, Measurable fun z : X × Y => ℓ (f z.1) z.2)
      (a b : ℝ) (_hbdd : ∀ f ∈ F, ∀ᵐ z ∂M, ℓ (f z.1) z.2 ∈ Set.Icc a b)
      (T : ℕ) (_hT : 0 < T) (fhat : (Fin T → X × Y) → X → Y') (_hfhat : IsERM ℓ F fhat),
      ∫ D, excessLoss M ℓ F hF (fhat D) ∂(dataLaw M T) ≤
        C * (b - a) * Real.sqrt (Real.log (F.card : ℝ) / (T : ℝ))) ∧
    (∀ (X : Type u) [MeasurableSpace X]
      (M : Measure (X × ℝ)) [IsProbabilityMeasure M]
      (F : Finset (X → ℝ)) (hF : F.Nonempty) (hmeas : ∀ f ∈ F, Measurable f)
      (hrange : ∀ f ∈ F, ∀ x, f x ∈ Set.Icc (0 : ℝ) 1)
      (hy : ∀ᵐ z ∂M, z.2 ∈ Set.Icc (0 : ℝ) 1)
      (_hspec : IsWellSpecified M F)
      (T : ℕ) (_hT : 0 < T) (fhat : (Fin T → X × ℝ) → X → ℝ) (_hfhat : IsERM sqLoss F fhat),
      ∫ D, excessLoss M sqLoss F hF (fhat D) ∂(dataLaw M T) ≤
        C * Real.log (F.card : ℝ) / (T : ℝ)) := by sorry

end FoundationsRL.StatLearning
