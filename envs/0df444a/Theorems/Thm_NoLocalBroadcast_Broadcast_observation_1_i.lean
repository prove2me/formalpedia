-- Prove2me | Theorems.Thm_NoLocalBroadcast_Broadcast_observation_1_i
-- name    : NoLocalBroadcast.Broadcast.observation_1_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T09:34:58.527285+00:00
-- url     : https://prove2.me/theorems/d6c7efb2-ec53-476d-87eb-4f5da2eaf912
-- title:
--   Observation 1(i) (p. 2) — I, I_CQ and I_CC are non-increasing under local channels Λ_A ⊗ Γ_B
-- statement:
--   Let $\rho$ be a state of a finite-dimensional bipartite system $A\otimes B$, and let $\Lambda_A:A\to A_1$ and $\Gamma_B:B\to B_1$ be channels into arbitrary finite-dimensional systems $A_1$, $B_1$. Then
--
--   $$I\big((\Lambda_A\otimes\Gamma_B)[\rho]\big)\le I(\rho),\qquad I_{CQ}\big((\Lambda_A\otimes\Gamma_B)[\rho]\big)\le I_{CQ}(\rho),\qquad I_{CC}\big((\Lambda_A\otimes\Gamma_B)[\rho]\big)\le I_{CC}(\rho).$$
--
--   Here $I$ is the quantum mutual information and $I_{CQ}$, $I_{CC}$ are the CQ and CC mutual informations of Definition 4. The three monotonicity statements are what allow, in the proofs of Theorems 2 and 3, to compare a state with its broadcast states.
--
--   **Formalization Note** Channels are finite normalized Kraus families; the local channel has the Kraus operators $K_k\otimes L_l$.
--
--   Differences from the source:
--   - reading: non-increasing under local operations → non-increasing under every product channel Λ_A ⊗ Γ_B : A ⊗ B → A₁ ⊗ B₁; reason: the paragraph before Observation 1 introduces 'local operations' as the local channels Λ_A ⊗ Γ_B of Definition 3's discussion; Theorem 2's proof applies it to Θ_A ⊗ Θ_B and to partial traces
--   - encoding: finite-dimensional systems A, B and quantum states → nonempty finite index types a, b; states are positive semidefinite trace-one matrices (QAlgorithms.IsDensityMatrix), A the first factor of a × b; reason: the paper works in finite dimension throughout; same instances
--   - encoding: local maps / channels (trace-preserving completely positive, footnote [21]) → finite normalized Kraus families K : Fin m → Matrix a₁ a ℂ, L : Fin n → Matrix b₁ b ℂ; the local channel Λ_A ⊗ Γ_B has the Kraus operators K k ⊗ₖ L l (localApply); reason: in finite dimension these are exactly the CPTP maps and their tensor products; same instances
--   - encoding: I_CQ, I_CC as maxima over measurement maps with an orthonormal register → sSup over POVMs with any finite number n of outcomes, the outcome written in the computational basis of Fin n; reason: the maximum is attained in finite dimension, so sSup is the paper's value; any other orthonormal register gives a unitarily equivalent state with the same entropies
--   - encoding: log of unspecified base in S(ρ) = −Tr ρ log ρ → QAlgorithms.vnEntropy, base 2; reason: every statement here is invariant under the base of the logarithm
-- source:
--   Piani, Horodecki & Horodecki, No-local-broadcasting theorem for quantum correlations, arXiv:0707.0848v2, p. 2, Observation 1(i)

import Mathlib
import Definitions.Def_NoLocalBroadcast_Broadcast_Model

namespace NoLocalBroadcast.Broadcast

open Matrix
open scoped Kronecker

/-- Observation 1(i), p. 2: `I`, `I_CQ` and `I_CC` do not increase under a local channel
`Λ_A ⊗ Γ_B : A ⊗ B → A₁ ⊗ B₁` (Kraus families `K`, `L`, arbitrary finite outputs). -/
theorem observation_1_i {a b a₁ b₁ : Type} [Fintype a] [DecidableEq a] [Nonempty a]
    [Fintype b] [DecidableEq b] [Nonempty b]
    [Fintype a₁] [DecidableEq a₁] [Fintype b₁] [DecidableEq b₁] {m n : ℕ}
    (K : Fin m → Matrix a₁ a ℂ) (L : Fin n → Matrix b₁ b ℂ)
    (hK : QAlgorithms.IsKrausFamily K) (hL : QAlgorithms.IsKrausFamily L)
    (ρ : Matrix (a × b) (a × b) ℂ) (hρ : QAlgorithms.IsDensityMatrix ρ) :
    mutualInfo (localApply K L ρ) ≤ mutualInfo ρ ∧
      I_CQ (localApply K L ρ) ≤ I_CQ ρ ∧
      I_CC (localApply K L ρ) ≤ I_CC ρ := by sorry

end NoLocalBroadcast.Broadcast
