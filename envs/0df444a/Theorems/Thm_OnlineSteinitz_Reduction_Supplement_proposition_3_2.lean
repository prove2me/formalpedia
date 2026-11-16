-- Prove2me | Theorems.Thm_OnlineSteinitz_Reduction_Supplement_proposition_3_2
-- name    : OnlineSteinitz.Reduction.Supplement.proposition_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T16:16:43.421202+00:00
-- url     : https://prove2.me/theorems/e554a409-0069-4708-9306-a2c63a33d80f
-- title:
--   Proposition 3.2 — greedy proportional routing with the exact constant
-- statement:
--   For every positive horizon $T$ and dimension $d$, run Algorithm 1 with greedy signing of $(v_t,1)/\sqrt2$ at every internal node. For every adaptive adversary generating Euclidean unit-ball vectors, with arbitrary initially unknown total,
--
--   $$\operatorname{res}_{\max}(v_\pi)\le \frac{\sqrt2+1}{1-\sqrt{2/3}}\sqrt T.$$
--
--   All output prefixes, including both endpoints, are covered simultaneously. The rule updates its proposed signed sum after every arrival even when the router overrides its destination. This arbitrary-total guarantee supplies the higher-dimensional deterministic upper bound after specializing to total zero.
--
--   Differences from the source:
--   - encoding: real Euclidean vectors and positions numbered 1 through T → the published Vec d and Run types with zero-based positions and Fin T arrivals; reason: the index shift preserves all streams, placements and prefixes including 0 and T
--   - encoding: every unit-ball stream, including adaptive streams → every causal adversary, assuming only that the vectors on its realized execution have norm at most one; reason: this quantifies every possible adaptive stream and imposes no zero-total or advance-total condition
-- source:
--   Russo–Wei, The Online Steinitz Problem, STOC 2027 submission #22 (2026 preprint), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/22.pdf; SHA-256 32ff14f15a94c95630765c77f4fa5a429fb294bcf03a9055ed67c60658769366; Proposition 3.2, PDF/printed p.14 (proof continues on the following pages)

import Definitions.Def_OnlineSteinitz_Reduction_Supplement_Rules

open MeasureTheory

namespace OnlineSteinitz.Reduction.Supplement

/-- Proposition 3.2, (3.2), pp.14–15. Arbitrary totals and adaptive inputs. -/
theorem proposition_3_2 :
    ∀ (T d : ℕ), 1 ≤ T → 1 ≤ d →
    ∀ adv : ℕ → List (ℕ × Vec d) → Vec d,
      (∀ p ∈ (adaptiveExecute (greedyRules T d) (fun _ => ()) adv).placed,
        ‖p.2‖ ≤ 1) →
      maxResidual (adaptiveExecute (greedyRules T d) (fun _ => ()) adv) ≤
        greedyConstant * Real.sqrt T := by sorry

end OnlineSteinitz.Reduction.Supplement
