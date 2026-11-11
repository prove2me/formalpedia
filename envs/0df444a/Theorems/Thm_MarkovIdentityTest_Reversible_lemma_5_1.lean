-- Prove2me | Theorems.Thm_MarkovIdentityTest_Reversible_lemma_5_1
-- name    : MarkovIdentityTest.Reversible.lemma_5_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T06:39:22.055617+00:00
-- url     : https://prove2.me/theorems/275fa9fd-421d-4c78-afcc-286155f0782e
-- title:
--   Lemma 5.1 — one retained row: $0\le\mathbb E W\le\ell\Pr(N\ge1)$ and $\mathbb E W^2\le 2d\ell^2\Pr(N\ge1)$
-- statement:
--   Consider a stopped row with the law (5.1): reached with probability $\rho=\Pr(N\ge1)$, return probability $s\in[0,1)$, returning law $r$, final law $e$, row law $q=sr+(1-s)e$. Let $\phi$ be a feature of a destination with values in $\mathbb R^D$, centred under $q$ ($\sum_yq_y\phi(y)=0$), with covariance $\Sigma_q=\sum_yq_y\phi(y)\phi(y)^\top\preceq\ell I$ (i.e. $u^\top\Sigma_qu\le\ell\|u\|^2$ for all $u$; $\ell\ge0$) and $\operatorname{rank}\Sigma_q\le d$. With $L=(N-1)_+$ and $W=\frac1L\sum_{a\ne b\le L}\langle\phi(Y_a),\phi(Y_b)\rangle$ ($W=0$ if $L=0$, and if the row is not reached),
--   $$0\le\mathbb EW\le\ell\Pr(N\ge1),\qquad\mathbb EW^2\le2d\ell^2\Pr(N\ge1),$$
--   and both expectations are finite. The bound does not depend on the expected number of returns to the row.
--
--   Differences from the source:
--
--   - generalization: the stopped row of a chain at a geometric time, whose law is (5.1) → any stopped row with law (5.1): s ∈ [0, 1), probability vectors r, e, q = s r + (1 − s) e, reach probability ρ ∈ [0, 1]; reason: the proof uses only (5.1); the paper applies the lemma to the two-state trace in Lemma 5.2 and notes (p. 24) that (5.1) holds under Markovian killing; chain rows are an instance by Eq. (5.1)
--   - reading: ℓ, the bound in Σ_q ⪯ ℓI → hypothesis 0 ≤ ℓ; reason: the proof treats ℓ = 0 and ℓ > 0; Σ_q ⪯ ℓI already forces ℓ ≥ 0 when D ≥ 1
--   - encoding: vector-valued ϕ, ⟨·,·⟩, Σ_q = Cov_q(ϕ) → ϕ : α → (Fin D → ℝ), dot product, Σ_q = ∑ q_y ϕ(y)ϕ(y)ᵀ; reason: ϕ is centred, so the covariance equals the second-moment matrix
--   - encoding: E W, E W² → ρ × (series against the law (5.1)), with absolute convergence asserted; reason: W = 0 when the row is not reached
-- source:
--   Jianhao Jia, Identity Testing of Markov Chains from a Single Trajectory, STOC 2027 submission (manuscript sha256 cf0995fc…), p. 25, Lemma 5.1

import Mathlib
import Definitions.Def_MarkovIdentityTest_Reversible_StoppedRow

set_option autoImplicit false

namespace MarkovIdentityTest.Reversible

/-- Lemma 5.1 (Jia, p. 25 / PDF 27), for an abstract stopped row with the law (5.1): return
probability `s ∈ [0, 1)`, returning law `r`, final law `e`, original row `q = s r + (1 - s) e`,
reach probability `ρ = Pr(N ≥ 1)`. `E W = ρ · E[W | N ≥ 1]` since `W = 0` off the reached event. -/
theorem lemma_5_1 {α : Type*} [Fintype α] (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s < 1)
    (r e : α → ℝ) (hr : ∀ y, 0 ≤ r y) (hr1 : ∑ y, r y = 1) (he : ∀ y, 0 ≤ e y)
    (he1 : ∑ y, e y = 1) (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    {D : ℕ} (ϕ : α → Fin D → ℝ) (ℓ : ℝ) (hℓ : 0 ≤ ℓ) (d : ℕ)
    (hmean : ∑ y, rowMixture s r e y • ϕ y = 0)
    (hcov : ∀ u : Fin D → ℝ,
      dotProduct u (Matrix.mulVec (featureCov (rowMixture s r e) ϕ) u) ≤ ℓ * dotProduct u u)
    (hrank : (featureCov (rowMixture s r e) ϕ).rank ≤ d) :
    StoppedRowIntegrable s r e (retainedScore ϕ) ∧
      StoppedRowIntegrable s r e (fun l y => retainedScore ϕ l y ^ 2) ∧
      0 ≤ ρ * stoppedRowExp s r e (retainedScore ϕ) ∧
      ρ * stoppedRowExp s r e (retainedScore ϕ) ≤ ℓ * ρ ∧
      ρ * stoppedRowExp s r e (fun l y => retainedScore ϕ l y ^ 2) ≤ 2 * d * ℓ ^ 2 * ρ := by sorry

end MarkovIdentityTest.Reversible
