-- Prove2me | Theorems.Thm_FreeSpencer_proposition_7_9
-- name    : FreeSpencer.proposition_7_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:10:34.792212+00:00
-- url     : https://prove2.me/theorems/8b525204-6e2c-4598-a2b9-65592d62c3ed
-- title:
--   Proposition 7.9, p.55 — verification with acceptance tests
-- statement:
--   Let $n\ge1$, $m\ge1$, $b\ge1$. Assume (7.2), (7.3) and the properties of the procedures. Every signing returned by Algorithm 3 satisfies
--   $$\Bigl\|\sum_i\sigma_iA_i\Bigr\|_{op}\le E(0,I_n)+(2+\sqrt2)(11.51K+64)\sqrt n,$$
--   and the probability of returning failure is at most $2^{-b}$. The bound is pathwise; only the failure event is probabilistic.
--
--   Differences from the source:
--   - generalization: the procedures of Algorithms 2 and 3 → every Procs with Procs.Spec; reason: Section 7.2 and Proposition 7.9 are stated for "the properties of the procedures"; the implemented procedures are one instance
--   - reading: "The total trace of discarded small eigenvalues is at most ℓ/1024" (p.50); the basis of W (p.50) → per call u ≤ 2δ(rank C − rank C′), and the App. F form of the basis: ½P_W ⪯ C, W ⊆ V, dim W ≥ 2 Tr C − rank C − |F| − 1; reason: these are what Lemma C.2, Lemma 7.1, Remark 7.2 and App. F.4 provide; the total follows, since the covariance range never grows
--   - reading: "Every returned signing" → every some σ in the support of the law of Algorithm 3, with σᵢ = ±1 stated; reason: the page: "This proves (7.14) pathwise"
--   - encoding: C on ℝ^{I₀}, starting at I_ℓ → C on ℝⁿ, starting at the diagonal projection on I₀; reason: Remark 7.2 (p.49): all n coordinates may be kept; the zero rows do not change η_C
-- source:
--   T. Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), Proposition 7.9, p.55; proof pp.55–56

import Mathlib
import Definitions.Def_FreeSpencer_fullRun
import Definitions.Def_FreeSpencer_Hyp72
open scoped Matrix Matrix.Norms.L2Operator

namespace FreeSpencer

/-- **Proposition 7.9** (Verification with acceptance tests), (7.14) pathwise and the failure bound.
Source: Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), Proposition 7.9, p.55; proof pp.55–56.

**Formalization Note** "Every returned signing" is every `some σ` in the support of the law of Algorithm 3,
for every procedures with the properties of Section 7.2. `K` comes from the mode, square or rectangular.
`E(0, I_n)` is `Epot par A 0 1`. The input is `n, m ≥ 1`, as in Section 7.2 (p.50); for
`n < 32` Algorithm 3 returns the all-positive signing (line 4). -/
theorem proposition_7_9 {n m b : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) (hb : 1 ≤ b)
    (A : Fin n → Matrix (Fin m) (Fin m) ℝ) (hsymm : ∀ i, (A i).IsSymm) (hA : ∀ i, ‖A i‖ ≤ 1)
    (P : Procs n m) (hP : P.Spec A (params n m))
    (h72 : Hyp72 A (params n m)) (h73 : Hyp73 A (params n m)) :
    (∀ σ : Fin n → ℝ, some σ ∈ (fullRun P A b).support → (∀ i, σ i = 1 ∨ σ i = -1) ∧
      ‖∑ i, σ i • A i‖ ≤ Epot (params n m) A 0 1 +
        (2 + Real.sqrt 2) * (11.51 * ((params n m).K : ℝ) + 64) * Real.sqrt n) ∧
    (fullRun P A b) none ≤ (1 / 2 : ENNReal) ^ b := by sorry

end FreeSpencer
