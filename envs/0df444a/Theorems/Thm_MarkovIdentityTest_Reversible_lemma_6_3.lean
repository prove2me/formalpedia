-- Prove2me | Theorems.Thm_MarkovIdentityTest_Reversible_lemma_6_3
-- name    : MarkovIdentityTest.Reversible.lemma_6_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T06:38:44.136951+00:00
-- url     : https://prove2.me/theorems/534b46cf-c449-4f06-b425-e24acc426e9f
-- title:
--   Lemma 6.3 — two-state local times: $\mathbb E_x(\sqrt{\lambda_i}-\sqrt{\lambda_j})^2\le 12(U_{ii}+U_{jj}-2U_{ij})$
-- statement:
--   Let $P$ be stochastic and reversible with respect to a strictly positive probability vector $\pi$, and $M>1$, $z=1-1/M$. In the holding-time model (the chain $P$ up to an independent positive geometric time of mean $M$, an independent unit exponential holding time before every observed transition, $\ell_i$ the total holding time at $i$), put $\lambda_i=\ell_i/\pi_i$ and $U=(I-zP)^{-1}\mathrm{diag}(\pi)^{-1}$. Then for every initial state $x$ and every pair $i\ne j$, $(\sqrt{\lambda_i}-\sqrt{\lambda_j})^2$ is integrable and
--   $$\mathbb E_x\big(\sqrt{\lambda_i}-\sqrt{\lambda_j}\big)^2\le12\,(U_{ii}+U_{jj}-2U_{ij}).$$
--
--   Differences from the source:
--
--   - encoding: holding times attached to the trajectory → ℓ_i = ∑_{k<N_i} E_{i,k} with E an independent Exp(1) family indexed by (state, k < t), given the discrete path; reason: the paper's total holding time at i is a sum of N_i independent unit exponentials given the path
--   - generalization: M = ⌈C₀ n/ε⌉ (an integer ≥ 2) → any real M > 1; reason: the proof uses only z = 1 − 1/M ∈ (0, 1); specializes
--   - reading: the strictly positive stationary distribution π satisfying detailed balance → every strictly positive probability vector π with detailed balance; reason: π need not be unique when P is reducible; the lemma holds for each choice
--   - encoding: E_x → series over t of integrals, with integrability of every inner integral and convergence asserted; reason: rules out a default value 0
-- source:
--   Jianhao Jia, Identity Testing of Markov Chains from a Single Trajectory, STOC 2027 submission (manuscript sha256 cf0995fc…), p. 34, Lemma 6.3 (model of §6.3.1, p. 33)

import Mathlib
import Definitions.Def_CEPolytopeHard_IsStochastic
import Definitions.Def_MarkovIdentityTest_Reversible_Discrepancy
import Definitions.Def_MarkovIdentityTest_Reversible_HoldingTime

set_option autoImplicit false

open CEPolytopeHard

namespace MarkovIdentityTest.Reversible

/-- Lemma 6.3 (Jia, p. 34 / PDF 36), in the holding-time model of §6.3.1: `λᵢ = ℓᵢ/πᵢ` and
`U = (I - zP)⁻¹ diag(π)⁻¹`, `z = 1 - 1/M`. -/
theorem lemma_6_3 {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (hP : IsStochastic P)
    (π : Fin n → ℝ) (hπ : IsReversibleWrt P π) (M : ℝ) (hM : 1 < M) (x i j : Fin n)
    (hij : i ≠ j) :
    HoldingIntegrable M P x
        (fun ℓ => (Real.sqrt (ℓ i / π i) - Real.sqrt (ℓ j / π j)) ^ 2) ∧
      holdingExp M P x (fun ℓ => (Real.sqrt (ℓ i / π i) - Real.sqrt (ℓ j / π j)) ^ 2)
        ≤ 12 * (normalizedGreen M P π i i + normalizedGreen M P π j j
          - 2 * normalizedGreen M P π i j) := by sorry

end MarkovIdentityTest.Reversible
