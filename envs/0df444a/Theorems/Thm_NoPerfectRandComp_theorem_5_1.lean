-- Prove2me | Theorems.Thm_NoPerfectRandComp_theorem_5_1
-- name    : NoPerfectRandComp.theorem_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:49:07.090975+00:00
-- url     : https://prove2.me/theorems/abc5e754-7066-4ca6-a50a-4a34fd0ae91a
-- title:
--   Theorem 5.1 — $\mathrm{R}(W_q\circ\hat M_q)/(\mathrm{R}(W_q)\mathrm{R}(\hat M_q))=\Theta(1/s)=\Theta(1/\log q)$
-- statement:
--   For $q = 2^s - 1$, the total Boolean functions $W_q$ and $\hat M_q$ are nonconstant and satisfy
--   $$
--   \frac{\mathrm{R}(W_q \circ \hat M_q)}{\mathrm{R}(W_q)\,\mathrm{R}(\hat M_q)} = \Theta\Big(\frac1s\Big) = \Theta\Big(\frac1{\log q}\Big),
--   $$
--   where composition places an independent copy of the inner function at every Boolean coordinate of the outer function. Consequently perfect randomized composition fails even when both functions are total.
--
--   **Formalization Note** $\Theta$ is explicit constants $0 < c \le C$ and a threshold $s_0$, uniform in the encodings, and the ratio is multiplied out: $c\,\mathrm{R}(W_q)\mathrm{R}(\hat M_q) \le s\,\mathrm{R}(W_q\circ\hat M_q) \le C\,\mathrm{R}(W_q)\mathrm{R}(\hat M_q)$, and the same with $\log_2 q$ in place of $s$.
--
--   Differences from the source:
--   - generalization: the explicitly specified W_q and M̂_q (one fixed encoding each) → W_q and M̂_q for every pair of admissible encodings, constants uniform in them; reason: every ingredient (Lemmas 4.9, 5.4, (19), (29)) holds for every admissible encoding, and the paper's encodings are admissible
--   - encoding: the ratio = Θ(1/s) = Θ(1/log q) for all sufficiently large s → explicit constants, a threshold s₀ and the multiplied-out inequalities; reason: R(W_q), R(M̂_q) ≥ 1, so the multiplied form is the ratio bound
-- source:
--   Meiburg, No Perfect Randomized Composition, arXiv:2610.31638 (held version, sha256 5122a74a…), Theorem 5.1, p.18 (proof pp.26–27)

import Mathlib
import Definitions.Def_OAI_Combinatorics_Sensitivity_Composition
import Definitions.Def_NoPerfectRandComp_Reps
import Definitions.Def_NoPerfectRandComp_IsNonconst
import Definitions.Def_NoPerfectRandComp_W
import Definitions.Def_NoPerfectRandComp_Mhat

namespace NoPerfectRandComp

/-- Theorem 5.1 of Meiburg, *No Perfect Randomized Composition*, arXiv:2610.31638 (held version, sha256 5122a74a…aeae3), p.18 (total–total failure of perfect composition): the total Boolean
functions `W_q` and `M̂_q`, with `q = 2ˢ − 1`, are nonconstant and satisfy
`R(W_q ∘ M̂_q) / (R(W_q) R(M̂_q)) = Θ(1/s) = Θ(1/log q)`.

**Formalization Note** `Θ` is explicit constants `0 < c ≤ C` and a threshold `s₀` ("all
sufficiently large s"), uniform in the encodings; the ratio is multiplied out:
`c R(W) R(M̂) ≤ s · R(W ∘ M̂) ≤ C R(W) R(M̂)`, and the same with `log₂ q` in place of `s`. Composition
places an independent copy of `M̂_q` at every Boolean coordinate of `W_q`. -/
theorem theorem_5_1 :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ s₀ : ℕ, ∀ s q : ℕ, s₀ ≤ s → q = 2 ^ s - 1 →
      ∀ (encW : Encoding (aq q) (WCell q)) (encM : Encoding (bq q) (PtrCell q)),
        IsNonconst (W q encW) ∧ IsNonconst (Mhat q encM) ∧
        c * (Rt (W q encW) : ℝ) * Rt (Mhat q encM) ≤
          s * Rt (OAI.Paper320.compose (W q encW) (Mhat q encM)) ∧
        (s : ℝ) * Rt (OAI.Paper320.compose (W q encW) (Mhat q encM)) ≤
          C * Rt (W q encW) * Rt (Mhat q encM) ∧
        c * (Rt (W q encW) : ℝ) * Rt (Mhat q encM) ≤
          Real.logb 2 q * Rt (OAI.Paper320.compose (W q encW) (Mhat q encM)) ∧
        Real.logb 2 q * Rt (OAI.Paper320.compose (W q encW) (Mhat q encM)) ≤
          C * Rt (W q encW) * Rt (Mhat q encM) := by sorry

end NoPerfectRandComp
