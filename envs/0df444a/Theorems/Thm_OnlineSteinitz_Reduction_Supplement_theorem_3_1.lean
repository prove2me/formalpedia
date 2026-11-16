-- Prove2me | Theorems.Thm_OnlineSteinitz_Reduction_Supplement_theorem_3_1
-- name    : OnlineSteinitz.Reduction.Supplement.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T16:17:21.461265+00:00
-- url     : https://prove2.me/theorems/e204195c-4d2a-45c9-ab8b-b9848b302c52
-- title:
--   Theorem 3.1 — deterministic online Steinitz upper bounds
-- statement:
--   There is an absolute constant $C>0$ such that for every $T\ge2$ and $d\ge1$, one deterministic causal algorithm, fixed before the stream, is valid and guarantees
--
--   $$\operatorname{res}_{\max}(v_\pi)\le C\begin{cases}\log T,&d=1,\\\sqrt T,&d\ge2,\end{cases}$$
--
--   against every adaptive adversary producing unit-ball vectors with total zero. The chosen algorithm is Algorithm 1 with the scalar ratio rule for $d=1$ and greedy augmented signing for $d\ge2$. The uniform constant is independent of horizon, dimension and input. These are both deterministic OSP upper-bound regimes, expressed constructively.
--
--   Differences from the source:
--   - encoding: real Euclidean vectors and positions numbered 1 through T → the published Vec d and Run types with zero-based positions and Fin T arrivals; reason: the index shift preserves all streams, placements and prefixes including 0 and T
--   - encoding: the optimal discrepancy bounds OSdet and OSrand → operational achievable guarantees, with one absolute constant before all instance parameters; reason: upper bounds exhibit a fixed causal rule; lower bounds apply to every valid rule and every uniformly achievable real radius, without assuming an attained optimum
-- source:
--   Russo–Wei, The Online Steinitz Problem, STOC 2027 submission #22 (2026 preprint), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/22.pdf; SHA-256 32ff14f15a94c95630765c77f4fa5a429fb294bcf03a9055ed67c60658769366; Theorem 3.1, PDF/printed p.13 (proof continues on the following pages)

import Definitions.Def_OnlineSteinitz_Reduction_Supplement_Bounds
import Definitions.Def_OnlineSteinitz_Reduction_Supplement_Rules

open MeasureTheory

namespace OnlineSteinitz.Reduction.Supplement

/-- Theorem 3.1, p.13, with scalar rule §3.1 and greedy rule §3.2. -/
theorem theorem_3_1 :
    ∃ C : ℝ, 0 < C ∧ ∀ (T d : ℕ), 2 ≤ T → 1 ≤ d →
      ValidOrdering (T := T) (upperOrdering T d) ∧
      DeterministicGuarantee (T := T) (upperOrdering T d)
        (C * deterministicRate T d) := by sorry

end OnlineSteinitz.Reduction.Supplement
