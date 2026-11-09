-- Prove2me | Theorems.Thm_LowRankDenoise432_OptimalProjector_lemma_3_2
-- name    : LowRankDenoise432.OptimalProjector.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:46:39.520528+00:00
-- url     : https://prove2.me/theorems/21b797c6-374a-42a2-8d50-902b5cc5d13e
-- title:
--   Lemma 3.2 — the error of a projection estimator splits into noise and bias
-- statement:
--   Let $\Pi$ be a real $d\times d$ orthogonal projector ($\Pi^\top=\Pi$, $\Pi^2=\Pi$), let $\bar c'\in\mathbb R^d$ be any centre, and let $c,\bar\varepsilon\in\mathbb R^d$ with $\bar y=c+\bar\varepsilon$. For the projection estimate $\hat c=\bar c'+\Pi(\bar y-\bar c')$,
--   $$\hat c-c=\Pi\bar\varepsilon-(I-\Pi)(c-\bar c'),\qquad \|\hat c-c\|^2=\|\Pi\bar\varepsilon\|^2+\|(I-\Pi)(c-\bar c')\|^2 .$$
--
--   The first term is the noise kept by the projector, the second the signal it discards; their orthogonality is what makes the error of every projection estimator split exactly. Theorem 3.3 takes expectations of this identity with $\bar c'=\bar c$.
--
--   **Formalization Note.** $\|v\|^2$ is $\sum_e v_e^2$. The statement is pointwise: it holds for all vectors, hence at every outcome of random inputs.
--
--   Differences from the source:
--   - generalization: Π an orthogonal projector independent of ε̄, with random c and ε̄ → a fixed orthogonal projector and arbitrary fixed vectors c, ε̄, c̄′; reason: the identity is algebraic and uses no independence; evaluating it at each outcome recovers the source's statement, including a random Π
--   - encoding: vectors in ℝᵈ with squared Euclidean norm → Fin d → ℝ with sqNorm v = ∑ e, v e ^ 2, including d = 0; reason: finite coordinate representation of the same vectors and norm; the identities remain valid in dimension zero
-- source:
--   Henry Aldridge-Krawciw, Irene Aldridge, Low-Rank Denoising for Predict-then-Optimize, STOC 2027 submission #432 (October 2026), source.pdf SHA-256 8d92579f841e1b4853ee9eecd477b739374858db635a23defcc3fb767b137889, PDF p.2, Lemma 3.2 (proof PDF p.6)

import Mathlib
import Definitions.Def_LowRankDenoise432_OptimalProjector_Model
open Matrix

namespace LowRankDenoise432.OptimalProjector

/-- Lemma 3.2 (PDF p.2): for an orthogonal projector `Q`, any centre `c'`, cost `c` and averaged
noise `ε̄`, the estimator `ĉ = c' + Q(ȳ − c')` with `ȳ = c + ε̄` satisfies
`ĉ − c = Q ε̄ − (I − Q)(c − c')` and `‖ĉ − c‖² = ‖Q ε̄‖² + ‖(I − Q)(c − c')‖²`. -/
theorem lemma_3_2 {d : ℕ} (Q : Matrix (Fin d) (Fin d) ℝ) (hQ : IsOrthProjector Q)
    (c' c εbar : Fin d → ℝ) :
    projEstimate Q c' (c + εbar) - c = Q *ᵥ εbar - (1 - Q) *ᵥ (c - c') ∧
      sqNorm (projEstimate Q c' (c + εbar) - c) =
        sqNorm (Q *ᵥ εbar) + sqNorm ((1 - Q) *ᵥ (c - c')) := by sorry

end LowRankDenoise432.OptimalProjector
