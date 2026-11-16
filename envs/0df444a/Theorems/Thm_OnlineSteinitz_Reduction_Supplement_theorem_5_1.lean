-- Prove2me | Theorems.Thm_OnlineSteinitz_Reduction_Supplement_theorem_5_1
-- name    : OnlineSteinitz.Reduction.Supplement.theorem_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T16:22:33.512253+00:00
-- url     : https://prove2.me/theorems/825c1acb-0fa2-4f01-961b-536a4135f0de
-- title:
--   Theorem 5.1 — deterministic and randomized online Steinitz lower bounds
-- statement:
--   There exists an absolute constant $c>0$ such that for every $T\ge2$ and $d\ge1$, every deterministic causal ordering algorithm has a fixed zero-sum unit-ball input satisfying
--
--   $$\operatorname{res}_{\max}(v_\pi)\ge c\begin{cases}\log T,&d=1,\\\sqrt T,&d\ge2.\end{cases}$$
--
--   For $d\ge2$ the input lies in the fixed span of the first two coordinate vectors. Moreover, for every $0<\delta\le1/2$, every randomized causal ordering algorithm and every real $\rho$ guaranteed with probability at least $1-\delta$ on every fixed legal input must satisfy, with $d_*=\min(d,T)$,
--
--   $$\rho\ge c\bigl(\log T+\sqrt{d_*\log(T/d_*)}\bigr).$$
--
--   All private probability spaces and measurable causal slot decisions are allowed. The randomized guarantee quantifies over fixed inputs outside the tape event, so hard inputs are oblivious and tape-independent. The common constant is uniform in $\delta$, algorithms, dimension and horizon. This is the complete printed lower-bound theorem, including the planar assertion.
--
--   Differences from the source:
--   - encoding: real Euclidean vectors and positions numbered 1 through T → the published Vec d and Run types with zero-based positions and Fin T arrivals; reason: the index shift preserves all streams, placements and prefixes including 0 and T
--   - encoding: arbitrary deterministic or randomized immediate ordering algorithms → history-dependent slot rules with validity on every promised stream; arbitrary private probability spaces and measurable fixed-history decisions; reason: full private tapes model persistent state and dependent randomness; no future input or discrepancy property is assumed
--   - encoding: the optimal discrepancy bounds OSdet and OSrand → operational achievable guarantees, with one absolute constant before all instance parameters; reason: upper bounds exhibit a fixed causal rule; lower bounds apply to every valid rule and every uniformly achievable real radius, without assuming an attained optimum
-- source:
--   Russo–Wei, The Online Steinitz Problem, STOC 2027 submission #22 (2026 preprint), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/22.pdf; SHA-256 32ff14f15a94c95630765c77f4fa5a429fb294bcf03a9055ed67c60658769366; Theorem 5.1, PDF/printed p.20 (proof continues on the following pages)

import Definitions.Def_OnlineSteinitz_Reduction_Supplement_Bounds
import Definitions.Def_OnlineSteinitz_Reduction_Supplement_Inputs

open MeasureTheory

namespace OnlineSteinitz.Reduction.Supplement

/-- Theorem 5.1, p.20: all deterministic, fixed-plane and randomized clauses. -/
theorem theorem_5_1 :
    ∃ c : ℝ, 0 < c ∧ ∀ (T d : ℕ), 2 ≤ T → 1 ≤ d →
      (∀ A : OrderingRule d Unit, ValidOrdering (T := T) A →
        ∃ v : Fin T → Vec d, LegalInput v ∧ (2 ≤ d → FixedPlane v) ∧
          c * deterministicRate T d ≤ maxResidual (orderingRun A () v)) ∧
      (∀ (δ ρ : ℝ), 0 < δ → δ ≤ 1 / 2 →
        ∀ (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
          (A : OrderingRule d Ω), ValidOrdering (T := T) A → MeasurableOrdering A →
          RandomizedGuarantee (T := T) μ A δ ρ →
          c * randomizedRate T d ≤ ρ) := by sorry

end OnlineSteinitz.Reduction.Supplement
