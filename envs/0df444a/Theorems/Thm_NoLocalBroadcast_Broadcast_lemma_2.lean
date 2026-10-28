-- Prove2me | Theorems.Thm_NoLocalBroadcast_Broadcast_lemma_2
-- name    : NoLocalBroadcast.Broadcast.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T09:35:11.919234+00:00
-- url     : https://prove2.me/theorems/563f1759-d175-425b-927b-aea09a9824b3
-- title:
--   Lemma 2 (p. 2) — if a local channel preserves the mutual information of ρ, local channels recover ρ
-- statement:
--   Let $\rho$ be a state of a finite-dimensional bipartite system $A\otimes B$, and let $\Lambda_A:A\to A_1$ and $\Gamma_B:B\to B_1$ be channels. If
--
--   $$I\big((\Lambda_A\otimes\Gamma_B)[\rho]\big)=I(\rho),$$
--
--   then there are channels $\Lambda^*_A:A_1\to A$ and $\Gamma^*_B:B_1\to B$ such that
--
--   $$(\Lambda^*_A\otimes\Gamma^*_B)\circ(\Lambda_A\otimes\Gamma_B)[\rho]=\rho .$$
--
--   The recovery is required on the given state $\rho$ only, not on every input. The lemma is the mutual-information, local-channel case of Petz's characterization of equality in the monotonicity of relative entropy; it is used in Theorems 1 and 2 to invert measurement maps and partial traces.
--
--   **Formalization Note** All maps, the recovery maps included, are finite normalized Kraus families (footnote [21]: every map of the paper is a channel). No assumption on the rank or support of $\rho$ is made.
--
--   Differences from the source:
--   - encoding: finite-dimensional systems A, B and quantum states → nonempty finite index types a, b; states are positive semidefinite trace-one matrices (QAlgorithms.IsDensityMatrix), A the first factor of a × b; reason: the paper works in finite dimension throughout; same instances
--   - encoding: local maps / channels (trace-preserving completely positive, footnote [21]) → finite normalized Kraus families K : Fin m → Matrix a₁ a ℂ, L : Fin n → Matrix b₁ b ℂ; the local channel Λ_A ⊗ Γ_B has the Kraus operators K k ⊗ₖ L l (localApply); reason: in finite dimension these are exactly the CPTP maps and their tensor products; same instances
--   - encoding: log of unspecified base in S(ρ) = −Tr ρ log ρ → QAlgorithms.vnEntropy, base 2; reason: every statement here is invariant under the base of the logarithm
-- source:
--   Piani, Horodecki & Horodecki, No-local-broadcasting theorem for quantum correlations, arXiv:0707.0848v2, p. 2, Lemma 2

import Mathlib
import Definitions.Def_NoLocalBroadcast_Broadcast_Model

namespace NoLocalBroadcast.Broadcast

open Matrix
open scoped Kronecker

/-- Lemma 2, p. 2: if a local channel `Λ_A ⊗ Γ_B` preserves the mutual information of `ρ`,
then local channels `Λ*_A : A₁ → A`, `Γ*_B : B₁ → B` undo it on `ρ`. -/
theorem lemma_2 {a b a₁ b₁ : Type} [Fintype a] [DecidableEq a] [Nonempty a]
    [Fintype b] [DecidableEq b] [Nonempty b]
    [Fintype a₁] [DecidableEq a₁] [Fintype b₁] [DecidableEq b₁] {m n : ℕ}
    (K : Fin m → Matrix a₁ a ℂ) (L : Fin n → Matrix b₁ b ℂ)
    (hK : QAlgorithms.IsKrausFamily K) (hL : QAlgorithms.IsKrausFamily L)
    (ρ : Matrix (a × b) (a × b) ℂ) (hρ : QAlgorithms.IsDensityMatrix ρ)
    (hI : mutualInfo (localApply K L ρ) = mutualInfo ρ) :
    ∃ (m' n' : ℕ) (K' : Fin m' → Matrix a a₁ ℂ) (L' : Fin n' → Matrix b b₁ ℂ),
      QAlgorithms.IsKrausFamily K' ∧ QAlgorithms.IsKrausFamily L' ∧
        localApply K' L' (localApply K L ρ) = ρ := by sorry

end NoLocalBroadcast.Broadcast
