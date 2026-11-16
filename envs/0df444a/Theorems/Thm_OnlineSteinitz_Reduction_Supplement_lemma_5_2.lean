-- Prove2me | Theorems.Thm_OnlineSteinitz_Reduction_Supplement_lemma_5_2
-- name    : OnlineSteinitz.Reduction.Supplement.lemma_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T16:19:21.543284+00:00
-- url     : https://prove2.me/theorems/ce1ff471-fe24-4d31-aec4-f72dd79ffe7f
-- title:
--   Lemma 5.2 — fixed-input deterministic lower bounds
-- statement:
--   There exists an absolute constant $c>0$ such that for every $T\ge2$, $d\ge1$ and deterministic causal ordering algorithm, there is a fixed zero-sum Euclidean unit-ball input with
--
--   $$\operatorname{res}_{\max}(v_\pi)\ge c\begin{cases}\log T,&d=1,\\\sqrt T,&d\ge2.\end{cases}$$
--
--   In dimension one the input is one of the scalar inputs $I_s$ from (5.2), with $1\le s\le\lfloor T/2\rfloor$. In every dimension at least two all its vectors lie in the fixed span of the first two coordinate vectors. The input may depend on the algorithm; it does not depend on any online future decisions. This statement supplies the deterministic part of Theorem 5.1.
--
--   Differences from the source:
--   - encoding: real Euclidean vectors and positions numbered 1 through T → the published Vec d and Run types with zero-based positions and Fin T arrivals; reason: the index shift preserves all streams, placements and prefixes including 0 and T
--   - encoding: arbitrary deterministic or randomized immediate ordering algorithms → history-dependent slot rules with validity on every promised stream; arbitrary private probability spaces and measurable fixed-history decisions; reason: full private tapes model persistent state and dependent randomness; no future input or discrepancy property is assumed
-- source:
--   Russo–Wei, The Online Steinitz Problem, STOC 2027 submission #22 (2026 preprint), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/22.pdf; SHA-256 32ff14f15a94c95630765c77f4fa5a429fb294bcf03a9055ed67c60658769366; Lemma 5.2, PDF/printed p.20 (proof continues on the following pages)

import Definitions.Def_OnlineSteinitz_Reduction_Supplement_Bounds
import Definitions.Def_OnlineSteinitz_Reduction_Supplement_Inputs

open MeasureTheory

namespace OnlineSteinitz.Reduction.Supplement

/-- Lemma 5.2, pp.20–21, including the scalar-family and fixed-plane clauses. -/
theorem lemma_5_2 :
    ∃ c : ℝ, 0 < c ∧ ∀ (T d : ℕ), 2 ≤ T → 1 ≤ d →
      ∀ A : OrderingRule d Unit, ValidOrdering (T := T) A →
        ∃ v : Fin T → Vec d, LegalInput v ∧
          (d = 1 → ∃ s : ℕ, 1 ≤ s ∧ s ≤ T / 2 ∧ v = cycleInput T d 1 s) ∧
          (2 ≤ d → FixedPlane v) ∧
          c * deterministicRate T d ≤ maxResidual (orderingRun A () v) := by sorry

end OnlineSteinitz.Reduction.Supplement
