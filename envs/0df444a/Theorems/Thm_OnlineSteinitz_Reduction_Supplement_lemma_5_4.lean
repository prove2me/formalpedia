-- Prove2me | Theorems.Thm_OnlineSteinitz_Reduction_Supplement_lemma_5_4
-- name    : OnlineSteinitz.Reduction.Supplement.lemma_5_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T16:20:32.775237+00:00
-- url     : https://prove2.me/theorems/47587c75-0590-4141-b748-7cb223ce46db
-- title:
--   Lemma 5.4 — strict randomized scalar lower bound
-- statement:
--   There exists an absolute constant $c>0$ such that for every $T\ge2$ and every randomized scalar causal ordering algorithm on an arbitrary private probability space, some fixed scalar input $I_s$ of (5.2), $1\le s\le\lfloor T/2\rfloor$, satisfies
--
--   $$\mathbb P\bigl(\operatorname{res}_{\max}(I_s)>c\log T\bigr)>\tfrac12.$$
--
--   Both inequalities are strict. The input is chosen outside the tape event and is therefore independent of the realized randomness. No independent-per-arrival or finite-tape restriction is imposed. This supplies the logarithmic term in the randomized lower bound.
--
--   Differences from the source:
--   - encoding: real Euclidean vectors and positions numbered 1 through T → the published Vec d and Run types with zero-based positions and Fin T arrivals; reason: the index shift preserves all streams, placements and prefixes including 0 and T
--   - encoding: arbitrary deterministic or randomized immediate ordering algorithms → history-dependent slot rules with validity on every promised stream; arbitrary private probability spaces and measurable fixed-history decisions; reason: full private tapes model persistent state and dependent randomness; no future input or discrepancy property is assumed
-- source:
--   Russo–Wei, The Online Steinitz Problem, STOC 2027 submission #22 (2026 preprint), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/22.pdf; SHA-256 32ff14f15a94c95630765c77f4fa5a429fb294bcf03a9055ed67c60658769366; Lemma 5.4, PDF/printed p.22 (proof continues on the following pages)

import Definitions.Def_OnlineSteinitz_Reduction_Supplement_Bounds
import Definitions.Def_OnlineSteinitz_Reduction_Supplement_Inputs

open MeasureTheory

namespace OnlineSteinitz.Reduction.Supplement

/-- Lemma 5.4, pp.22–23. Both inequalities are strict; the input precedes the tape. -/
theorem lemma_5_4 :
    ∃ c : ℝ, 0 < c ∧ ∀ T : ℕ, 2 ≤ T →
      ∀ (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (A : OrderingRule 1 Ω), ValidOrdering (T := T) A → MeasurableOrdering A →
        ∃ v : Fin T → Vec 1, ScalarFamily v ∧ LegalInput v ∧
          (1 / 2 : ENNReal) < μ {ω |
            c * Real.log T < maxResidual (orderingRun A ω v)} := by sorry

end OnlineSteinitz.Reduction.Supplement
