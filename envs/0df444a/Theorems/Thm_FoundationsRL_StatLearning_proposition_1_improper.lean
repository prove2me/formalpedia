-- Prove2me | Theorems.Thm_FoundationsRL_StatLearning_proposition_1_improper
-- name    : FoundationsRL.StatLearning.proposition_1_improper
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:19:14.09141+00:00
-- url     : https://prove2.me/theorems/bc160e71-c2c9-4f3a-bdd9-ea6456f3ab6e
-- title:
--   Proposition 1, "In addition" clause: a different algorithm achieves $\log|\mathcal F|/T$ (corrected: range $[0,1]$ for square loss; companion of `proposition_1`)
-- statement:
--   This is the closing clause of Proposition 1; Parts 1 and 2 are the goal theorem `FoundationsRL.StatLearning.proposition_1`. There exists an algorithm, chosen knowing only the finite class $\mathcal F$ and the horizon $T$, whose output $\widehat f$ satisfies a bound of order
--
--   $$
--   \mathrm{comp}(\mathcal F,T)=\frac{\log|\mathcal F|}{T}
--   $$
--
--   in both of the following settings, with no well-specification assumption and one absolute constant $C>0$.
--
--   1. **Square loss regression.** If $\mathcal F$ consists of measurable functions $\mathcal X\to[0,1]$, the algorithm outputs a $[0,1]$-valued predictor and, for every distribution with $y\in[0,1]$ almost surely, $\mathbb E[\mathcal E(\widehat f)]\le C\log|\mathcal F|/T$.
--   2. **Conditional density estimation.** If $\mathcal F$ consists of conditional densities with respect to a $\sigma$-finite measure $\nu$, the algorithm outputs a conditional density, and for every distribution under which $(\log f)_+$ is integrable for each $f\in\mathcal F$ and every $f^\star\in\mathcal F$ of finite log-loss risk, the risk of $\widehat f$ is finite and
--
--   $$
--   \mathbb E\big[L(\widehat f)\big]\le L(f^\star)+\frac{C\log|\mathcal F|}{T}.
--   $$
--
--   The algorithm may be improper: $\widehat f$ need not belong to $\mathcal F$. Unlike ERM, it has the fast rate without realizability.
--
--   **Formalization Note** The algorithm is jointly measurable in the dataset and the feature, so that the population loss of its output is a measurable function of the dataset. For the log loss, $f^\star$ having finite risk means $f^\star>0$ almost surely and $\log f^\star$ integrable.
--
--   Differences from the source:
--   - correction: square loss on Y = Y′ = ℝ → F and the output take values in [0, 1], and y ∈ [0, 1] almost surely, as in Exercise 1 (p. 19); reason: no absolute constant exists on ℝ: rescaling y and F by c multiplies the excess square loss by c² and fixes log|F|/T, and an algorithm has positive expected excess loss on some instance with |F| = 2
--   - encoding: ≲ / an absolute constant → ∃ C > 0 quantified before all types and data; reason: the notes' meaning of an absolute constant
--   - reading: there exists a (different) algorithm → for each F and T there is a measurable A, chosen before the distribution; reason: an algorithm does not see the distribution and is applied to a given class and sample size
--   - encoding: Y′ = Δ(Y) with an implicit reference measure → densities with respect to a σ-finite reference measure ν, and the output is again a density; reason: ν is implicit in "conditional density" (Remark 1); counting measure gives the discrete case
--   - encoding: E[E(f̂)] ≲ log|F|/T for the log loss, with E(f̂) = L(f̂) − min_F L → E[L(f̂)] ≤ L(f⋆) + C log|F|/T for every f⋆ ∈ F of finite risk; reason: L can be +∞ on members of F, so it is not a real number; the minimum is attained at such an f⋆, or else every member has infinite risk and the claim is empty
--   - encoding: L(f) taken for granted → (log f)₊ integrable for each f ∈ F; reason: this is exactly L(f) > −∞ being well defined; it is automatic for discrete Y
--   - encoding: measurability left implicit → members of the class are measurable (ℓ ∘ f measurable); reason: the field's standing convention; the expectations are undefined otherwise
--   - encoding: T not stated → T ≥ 1; reason: the sample mean and the bound divide by T
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, Proposition 1, closing clause, p. 9

import Mathlib
import Definitions.Def_FoundationsRL_StatLearning_excessLoss
import Definitions.Def_FoundationsRL_StatLearning_popLoss
import Definitions.Def_FoundationsRL_StatLearning_sqLoss
import Definitions.Def_FoundationsRL_StatLearning_logLoss
import Definitions.Def_FoundationsRL_StatLearning_dataLaw
import Definitions.Def_FoundationsRL_StatLearning_IsCondDensity
open MeasureTheory
universe u v

namespace FoundationsRL.StatLearning

/-- **Proposition 1, the "In addition" clause.** There exists a (different) algorithm that achieves
`comp(F, T) = log|F|/T` for both square loss regression and conditional density estimation, even
when the problem is not well-specified. Parts 1 and 2 of the proposition are
`FoundationsRL.StatLearning.proposition_1`.
Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision Making*, arXiv:2312.16730v1, Proposition 1, p. 9.

**Formalization Note.** `≲` is `∃ C > 0`, chosen before all types and data. The algorithm `A` is
chosen from `F` and `T` before the distribution `M`, as an algorithm must be, and it may be improper:
`A D` need not lie in `F`. It is jointly measurable in dataset and feature, which makes `L(A D)` a
measurable function of the dataset.

*Square loss.* Range `[0, 1]`, as in Part 2 of `proposition_1`. `A D` takes values in `[0, 1]`, so
`L(A D)` is a genuine expectation.

*Conditional density estimation.* Predictors are conditional densities with respect to a
reference measure `ν` (`IsCondDensity`), and so are the outputs `A D`. The risk `L(f) = E[−log f(y|x)]`
of a density is an extended real, which can be `+∞` for a member of `F`, so `E[E(f̂)] ≤ …` cannot be
written with a real `min`. Instead the conclusion is `E[L(A D)] ≤ L(f⋆) + C log|F|/T` for every
`f⋆ ∈ F` of finite risk, which is the same inequality: the minimum over `F` is attained at such an
`f⋆`, unless every member has infinite risk and there is nothing to prove. The hypothesis that
`(log f)⁺` is integrable for every `f ∈ F` says that `L(f) > −∞` is well defined; it is automatic
on discrete `Y`, where densities are at most `1`. The conclusion also states that `L(A D)` is a
genuine finite expectation (`A D > 0` almost surely, `log A D` integrable) and integrable in `D`. -/
theorem proposition_1_improper : ∃ C : ℝ, 0 < C ∧
    (∀ (X : Type u) [MeasurableSpace X] (F : Finset (X → ℝ)) (hF : F.Nonempty)
      (_hmeas : ∀ f ∈ F, Measurable f) (_hrange : ∀ f ∈ F, ∀ x, f x ∈ Set.Icc (0 : ℝ) 1)
      (T : ℕ) (_hT : 0 < T),
      ∃ A : (Fin T → X × ℝ) → X → ℝ,
        Measurable (fun p : (Fin T → X × ℝ) × X => A p.1 p.2) ∧
        (∀ D x, A D x ∈ Set.Icc (0 : ℝ) 1) ∧
        ∀ (M : Measure (X × ℝ)) [IsProbabilityMeasure M],
          (∀ᵐ z ∂M, z.2 ∈ Set.Icc (0 : ℝ) 1) →
          ∫ D, excessLoss M sqLoss F hF (A D) ∂(dataLaw M T) ≤
            C * Real.log (F.card : ℝ) / (T : ℝ)) ∧
    (∀ (X : Type u) (Y : Type v) [MeasurableSpace X] [MeasurableSpace Y]
      (ν : Measure Y) [SigmaFinite ν] (F : Finset (X → Y → ℝ)) (_hF : F.Nonempty)
      (_hdens : ∀ f ∈ F, IsCondDensity ν f)
      (T : ℕ) (_hT : 0 < T),
      ∃ A : (Fin T → X × Y) → X → Y → ℝ,
        Measurable (fun p : (Fin T → X × Y) × X × Y => A p.1 p.2.1 p.2.2) ∧
        (∀ D, IsCondDensity ν (A D)) ∧
        ∀ (M : Measure (X × Y)) [IsProbabilityMeasure M],
          (∀ f ∈ F, Integrable (fun z : X × Y => max 0 (Real.log (f z.1 z.2))) M) →
          ∀ fstar ∈ F, (∀ᵐ z ∂M, 0 < fstar z.1 z.2) →
            Integrable (fun z : X × Y => logLoss (fstar z.1) z.2) M →
            (∀ D, (∀ᵐ z ∂M, 0 < A D z.1 z.2) ∧
              Integrable (fun z : X × Y => logLoss (A D z.1) z.2) M) ∧
            Integrable (fun D => popLoss M logLoss (A D)) (dataLaw M T) ∧
            ∫ D, popLoss M logLoss (A D) ∂(dataLaw M T) ≤
              popLoss M logLoss fstar + C * Real.log (F.card : ℝ) / (T : ℝ)) := by sorry

end FoundationsRL.StatLearning
