-- Prove2me | Theorems.Thm_GEGIAMP_Relative_lemma_8_16
-- name    : GEGIAMP.Relative.lemma_8_16
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T15:51:38.09379+00:00
-- url     : https://prove2.me/theorems/e143d726-128d-4d29-96b0-f51cdd442d1b
-- title:
--   Lemma 8.16 — energy loss from clipping
-- statement:
--   For symmetric $A$ and $v=\mathrm{clip}(f,[-1,1]^N)$, $|H_N(f)-H_N(v)|/N\le\frac{\|A\|}{2}\frac{\|f-v\|}{\sqrt N}\Big(\frac{\|f\|}{\sqrt N}+\frac{\|v\|}{\sqrt N}\Big)$ (8.84).
--
--   Differences from the source:
--   - encoding: ‖A‖, the induced operator norm → the operator norm of `Matrix.toEuclideanCLM A` on Euclidean space; reason: the same norm
--   - encoding: dimension N (≥ 1 implicitly) → every N : ℕ; reason: at N = 0 both sides are 0 (Lean’s x/0 = 0), so nothing is added
-- source:
--   Herman, Chakrabarti, Kim, Ozgul (2026), A Fully Polynomial Approximation Algorithm for the Sherrington–Kirkpatrick Model, arXiv:2611.05446v1 (version not printed; held file SHA-256 ea6508afbf5e8771a5353c9c9ce9df52a08608793fb812fc9ba947719fd5658e), Lemma 8.16, p. 58

import Mathlib
import Definitions.Def_GEGIAMP_Relative_Model

open MeasureTheory ProbabilityTheory OAI.ZeroTemperatureSK
open scoped ENNReal NNReal Topology

namespace GEGIAMP.Relative

/-- **Lemma 8.16** (energy loss from clipping; Herman, Chakrabarti, Kim, Ozgul (2026), arXiv:2611.05446v1, SHA-256 ea6508af…5658e, p. 58). For symmetric `A` and
`v = clip(f, [−1,1]^N)`,
`|H_N(f) − H_N(v)|/N ≤ (‖A‖/2) (‖f − v‖/√N) ((‖f‖ + ‖v‖)/√N)` (8.84). -/
theorem lemma_8_16 (N : ℕ) (A : Fin N → Fin N → ℝ) (hA : IsSymm A) (f : Fin N → ℝ) :
    |H A f - H A (clipVec f)| / N ≤
      opNorm A / 2 * (vnorm (fun i => f i - clipVec f i) / Real.sqrt N) *
        ((vnorm f + vnorm (clipVec f)) / Real.sqrt N) := by sorry

end GEGIAMP.Relative
