-- Prove2me | Theorems.Thm_FoundationsRL_StatLearning_lemma_1
-- name    : FoundationsRL.StatLearning.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:19:04.407857+00:00
-- url     : https://prove2.me/theorems/f4e57b4b-2fc3-40cc-bdb1-fd1f0da9b4cf
-- title:
--   Lemma 1 — excess square loss equals $L^2$ distance to the regression function
-- statement:
--   Consider the square loss with $\mathcal Y=\mathbb R$ and a finite class $\mathcal F$, and suppose the problem is well-specified, with regression function $f^\star\in\mathcal F$. Then for every $f:\mathcal X\to\mathbb R$,
--
--   $$
--   \mathcal E(f)=\mathbb E_x\big[(f(x)-f^\star(x))^2\big].
--   $$
--
--   Any predictor with low excess loss therefore estimates the regression function, so prediction and estimation coincide in this setting.
--
--   **Formalization Note** $\mathbb E_x$ is the integral against the marginal law of $x$. The outcome, the members of $\mathcal F$ and $f$ are square-integrable.
--
--   Differences from the source:
--   - encoding: for all f : X → Y → f, every member of F and the outcome y are square-integrable; reason: the losses in (1.7) must be real numbers; a Bochner integral of a non-integrable function is the junk 0
--   - encoding: f⋆ is in F → a version of the conditional expectation E[y|x] is in F; reason: a conditional expectation is defined only up to a null set
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, Lemma 1, (1.8), p. 9

import Mathlib
import Definitions.Def_FoundationsRL_StatLearning_excessLoss
import Definitions.Def_FoundationsRL_StatLearning_sqLoss
import Definitions.Def_FoundationsRL_StatLearning_IsRegressionFunction
open MeasureTheory

namespace FoundationsRL.StatLearning

/-- **Lemma 1** (excess square loss is the `L²` distance to the regression function).
For the square loss, if the problem is well-specified, then for all `f`,
`E(f) = E_x[(f(x) − f⋆(x))²]` (1.8).
Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision Making*, arXiv:2312.16730v1, Lemma 1, (1.8), p. 9.

**Formalization Note.** `Y = ℝ` as in the notes, with no range restriction. `f`, the members of `F`
and the outcome are square-integrable, which is what makes `L(f)` and every `L(f')` real numbers
(a Bochner integral of a non-integrable function would be the junk `0`). `M.fst` is the law of `x`. -/
theorem lemma_1 {X : Type*} [MeasurableSpace X] (M : Measure (X × ℝ)) [IsProbabilityMeasure M]
    (F : Finset (X → ℝ)) (hF : F.Nonempty)
    (hy : MemLp (fun z : X × ℝ => z.2) 2 M) (hFL2 : ∀ g ∈ F, MemLp g 2 M.fst)
    (fstar : X → ℝ) (hfstar : fstar ∈ F) (hreg : IsRegressionFunction M fstar)
    (f : X → ℝ) (hf : MemLp f 2 M.fst) :
    excessLoss M sqLoss F hF f = ∫ x, (f x - fstar x) ^ 2 ∂M.fst := by sorry

end FoundationsRL.StatLearning
