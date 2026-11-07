-- Prove2me | Theorems.Thm_FreeSpencer_corollary_10_2
-- name    : FreeSpencer.corollary_10_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:10:16.170014+00:00
-- url     : https://prove2.me/theorems/e5792070-1729-4739-a208-0b00d56dcf38
-- title:
--   Corollary 10.2, p.65 — the rectangular part of Theorem 1.1
-- statement:
--   For $m>n\ge1$ and $b\ge1$, Algorithm 3 returns a signing of discrepancy at most
--   $$4000\sqrt{n(1+\log(2m/n))},$$
--   except with probability at most $2^{-b}$ of returning failure. For $n<32$ this is the all-positive signing, and for $n\ge32$ the rectangular mode of Appendix C.1.
--
--   Differences from the source:
--   - generalization: the procedures of Algorithms 2 and 3 → every Procs with Procs.Spec; reason: Section 7.2 and Proposition 7.9 are stated for "the properties of the procedures"; the implemented procedures are one instance
--   - reading: "The total trace of discarded small eigenvalues is at most ℓ/1024" (p.50); the basis of W (p.50) → per call u ≤ 2δ(rank C − rank C′), and the App. F form of the basis: ½P_W ⪯ C, W ⊆ V, dim W ≥ 2 Tr C − rank C − |F| − 1; reason: these are what Lemma C.2, Lemma 7.1, Remark 7.2 and App. F.4 provide; the total follows, since the covariance range never grows
--   - reading: "returns a signing of discrepancy at most …" → every some σ in the support of the law, with σᵢ = ±1 stated; reason: the bound comes from (7.14), which is pathwise
--   - encoding: C on ℝ^{I₀}, starting at I_ℓ → C on ℝⁿ, starting at the diagonal projection on I₀; reason: Remark 7.2 (p.49): all n coordinates may be kept; the zero rows do not change η_C
-- source:
--   T. Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), Corollary 10.2, p.65; proof pp.65–66

import Mathlib
import Definitions.Def_FreeSpencer_fullRun
open scoped Matrix Matrix.Norms.L2Operator

namespace FreeSpencer

/-- **Corollary 10.2** (The rectangular part of Theorem 1.1). Source: Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), Corollary 10.2, p.65;
proof pp.65–66.

**Formalization Note** `m > n ≥ 1`. For `n < 32` the algorithm returns the all-positive signing, and for
`n ≥ 32` it runs the rectangular mode of p.77, for every procedures with the properties of Section 7.2.
The bound is pathwise, on every returned signing, as in (7.14). (7.2) and (7.3) are derived on the page
from Proposition 10.1 and (10.2), so they are not hypotheses. -/
theorem corollary_10_2 {n m b : ℕ} (hn : 1 ≤ n) (hmn : n < m) (hb : 1 ≤ b)
    (A : Fin n → Matrix (Fin m) (Fin m) ℝ) (hsymm : ∀ i, (A i).IsSymm) (hA : ∀ i, ‖A i‖ ≤ 1)
    (P : Procs n m) (hP : P.Spec A (params n m)) :
    (∀ σ : Fin n → ℝ, some σ ∈ (fullRun P A b).support → (∀ i, σ i = 1 ∨ σ i = -1) ∧
      ‖∑ i, σ i • A i‖ ≤
        4000 * Real.sqrt ((n : ℝ) * (1 + Real.log (2 * (m : ℝ) / (n : ℝ))))) ∧
    (fullRun P A b) none ≤ (1 / 2 : ENNReal) ^ b := by sorry

end FreeSpencer
