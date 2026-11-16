-- Prove2me | Theorems.Thm_OnlineSteinitz_Reduction_Supplement_remark_5_3
-- name    : OnlineSteinitz.Reduction.Supplement.remark_5_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T16:18:17.230434+00:00
-- url     : https://prove2.me/theorems/98b15ac9-39c3-4366-ab1b-9e46e8d99016
-- title:
--   Remark 5.3 — one-cycle lower bound for every ordering
-- statement:
--   There is an absolute constant $c>0$ such that for all $T\ge2$ and $d\ge1$, set $q=\min(d,\lfloor T/2\rfloor)$ and let $I_1$ contain one cycle of $e_1,\ldots,e_q$ followed by $T-q$ copies of $-\mathbf1_q/(T-q)$, embedded in $\mathbb R^d$. This is a zero-sum unit-ball input, and every ordering satisfies
--
--   $$\operatorname{res}_{\max}(I_1)\ge c\sqrt{\min(d,T)}.$$
--
--   The quantifier includes offline permutations and therefore every online algorithm. This bound supplies the small-horizon and large-dimension cases in the later lower bounds.
--
--   Differences from the source:
--   - encoding: real Euclidean vectors and positions numbered 1 through T → the published Vec d and Run types with zero-based positions and Fin T arrivals; reason: the index shift preserves all streams, placements and prefixes including 0 and T
-- source:
--   Russo–Wei, The Online Steinitz Problem, STOC 2027 submission #22 (2026 preprint), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/22.pdf; SHA-256 32ff14f15a94c95630765c77f4fa5a429fb294bcf03a9055ed67c60658769366; Remark 5.3, PDF/printed p.22

import Definitions.Def_OnlineSteinitz_Reduction_Supplement_Inputs

open MeasureTheory

namespace OnlineSteinitz.Reduction.Supplement

/-- Remark 5.3, p.22: every permutation of the constructed one-cycle input. -/
theorem remark_5_3 :
    ∃ c : ℝ, 0 < c ∧ ∀ (T d : ℕ), 2 ≤ T → 1 ≤ d →
      LegalInput (cycleInput T d (min d (T / 2)) 1) ∧
      ∀ π : Equiv.Perm (Fin T),
        c * Real.sqrt (min d T : ℕ) ≤
          maxResidual (permutationRun (cycleInput T d (min d (T / 2)) 1) π) := by sorry

end OnlineSteinitz.Reduction.Supplement
