-- Prove2me | Theorems.Thm_MarkovIdentityTest_Reversible_corollary_5_3
-- name    : MarkovIdentityTest.Reversible.corollary_5_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T06:39:21.258129+00:00
-- url     : https://prove2.me/theorems/78c17062-a76c-4f50-95f1-80427b46fdcb
-- title:
--   Corollary 5.3 — $\mathbb E(\sum_iW_i)^2\le\ell^2(2\sum_id_i+4n(n-1))\le 6\ell^2n(n-1)$
-- statement:
--   In the setting of Lemma 5.2, take any collection $S$ of rows, and for each $i\in S$ a destination feature $\phi_i$ centred under $Q_i$ with covariance $\preceq\ell I$ ($\ell\ge0$) and rank at most $d_i$. Then $(\sum_{i\in S}W_i)^2$ is integrable and
--   $$\mathbb E\Big(\sum_{i\in S}W_i\Big)^2\le\ell^2\Big(2\sum_{i\in S}d_i+4n(n-1)\Big).$$
--   Since every row has at most $n$ possible destinations, also $\mathbb E(\sum_{i\in S}W_i)^2\le6\ell^2n(n-1)$.
--
--   Differences from the source:
--
--   - encoding: any collection of rows → a Finset S of rows; reason: notation only
--   - encoding: if every row has at most n possible destinations → second bound stated without that hypothesis; reason: destinations range over Fin n, so the hypothesis always holds
--   - reading: ℓ, the covariance bound → hypothesis 0 ≤ ℓ; reason: implicit in the paper
--   - encoding: E at the geometric time → series over t with absolute convergence asserted; M ∈ ℝ, M ≥ 1; reason: same law; integrability rules out a default value 0
-- source:
--   Jianhao Jia, Identity Testing of Markov Chains from a Single Trajectory, STOC 2027 submission (manuscript sha256 cf0995fc…), p. 27, Corollary 5.3

import Mathlib
import Definitions.Def_CEPolytopeHard_IsStochastic
import Definitions.Def_MarkovIdentityTest_Reversible_Trajectory
import Definitions.Def_MarkovIdentityTest_Reversible_StoppedRow

set_option autoImplicit false

open CEPolytopeHard

namespace MarkovIdentityTest.Reversible

/-- Corollary 5.3 (Jia, p. 27 / PDF 29): for any collection `S` of rows with centred features
`ϕ i` of covariance `⪯ ℓI` and rank `≤ d i`, `E(∑_{i ∈ S} Wᵢ)² ≤ ℓ²(2 ∑ dᵢ + 4n(n-1))`, and
`≤ 6ℓ²n(n-1)` since every row has at most `n` possible destinations. -/
theorem corollary_5_3 {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : IsStochastic Q) (M : ℝ)
    (hM : 1 ≤ M) (x : Fin n) (S : Finset (Fin n)) {D : Fin n → ℕ}
    (ϕ : (i : Fin n) → Fin n → Fin (D i) → ℝ) (ℓ : ℝ) (hℓ : 0 ≤ ℓ) (d : Fin n → ℕ)
    (hmean : ∀ i ∈ S, ∑ y, Q i y • ϕ i y = 0)
    (hcov : ∀ i ∈ S, ∀ u : Fin (D i) → ℝ,
      dotProduct u (Matrix.mulVec (featureCov (Q i) (ϕ i)) u) ≤ ℓ * dotProduct u u)
    (hrank : ∀ i ∈ S, (featureCov (Q i) (ϕ i)).rank ≤ d i) :
    GeomIntegrable M Q x (fun _ ω => (∑ i ∈ S, chainRowScore (ϕ i) i ω) ^ 2) ∧
      geomExp M Q x (fun _ ω => (∑ i ∈ S, chainRowScore (ϕ i) i ω) ^ 2)
        ≤ ℓ ^ 2 * (2 * ∑ i ∈ S, (d i : ℝ) + 4 * n * (n - 1)) ∧
      geomExp M Q x (fun _ ω => (∑ i ∈ S, chainRowScore (ϕ i) i ω) ^ 2)
        ≤ 6 * ℓ ^ 2 * n * (n - 1) := by sorry

end MarkovIdentityTest.Reversible
