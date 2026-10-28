-- Prove2me | Theorems.Thm_NoLocalBroadcast_Broadcast_theorem_2
-- name    : NoLocalBroadcast.Broadcast.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T09:35:11.58357+00:00
-- url     : https://prove2.me/theorems/6809b273-99d5-4690-bab7-f6e7d937fc6c
-- title:
--   Theorem 2 (p. 3) — ρ is LB iff some broadcast state has the same mutual information; every such broadcast state is a local image of ρ
-- statement:
--   Let $\rho=\rho_{AB}$ be a state of a finite-dimensional bipartite system, and let $A'$, $B'$ be copies of $A$, $B$. Then
--
--   1. $\rho$ is locally broadcastable if and only if there is a broadcast state $\sigma_{AA',BB'}$ for $\rho$ with
--   $$I(\sigma_{AA':BB'})=I(\rho_{A:B});$$
--   2. every broadcast state $\sigma_{AA',BB'}$ for $\rho$ with $I(\sigma_{AA':BB'})=I(\rho_{A:B})$ is of the form $(\Theta_A\otimes\Theta_B)[\rho]$ for some channels $\Theta_A:A\to AA'$, $\Theta_B:B\to BB'$.
--
--   Here $I(\sigma_{AA':BB'})$ is the mutual information across the cut between the parties $(A,A')$ and $(B,B')$. The theorem reduces local broadcastability to the existence of a broadcast state with the same mutual information as $\rho$.
--
--   **Formalization Note** A two-copy operator is indexed $((x,x'),(y,y'))$; a broadcast state is a state whose reductions to $AB$ and to $A'B'$ both equal $\rho$.
--
--   Differences from the source:
--   - encoding: finite-dimensional systems A, B and quantum states → nonempty finite index types a, b; states are positive semidefinite trace-one matrices (QAlgorithms.IsDensityMatrix), A the first factor of a × b; reason: the paper works in finite dimension throughout; same instances
--   - encoding: local maps / channels (trace-preserving completely positive, footnote [21]) → finite normalized Kraus families K : Fin m → Matrix a₁ a ℂ, L : Fin n → Matrix b₁ b ℂ; the local channel Λ_A ⊗ Γ_B has the Kraus operators K k ⊗ₖ L l (localApply); reason: in finite dimension these are exactly the CPTP maps and their tensor products; same instances
--   - encoding: the two-copy system (AA′)(BB′) with copies X = AB, Y = A′B′ → matrices indexed by ((x, x′), (y, y′)) ∈ (a × a) × (b × b); A′, B′ have the types of A, B; the cut AA′ : BB′ is the outer product; σ_X = traceCopies σ, σ_Y = traceOriginals σ; reason: Lean carrier convention; same operators
--   - encoding: log of unspecified base in S(ρ) = −Tr ρ log ρ → QAlgorithms.vnEntropy, base 2; reason: every statement here is invariant under the base of the logarithm
-- source:
--   Piani, Horodecki & Horodecki, No-local-broadcasting theorem for quantum correlations, arXiv:0707.0848v2, p. 3, Theorem 2

import Mathlib
import Definitions.Def_NoLocalBroadcast_Broadcast_Model

namespace NoLocalBroadcast.Broadcast

open Matrix
open scoped Kronecker

/-- Theorem 2, p. 3: `ρ` is LB iff some broadcast state `σ_{AA′,BB′}` for `ρ` has
`I(σ_{AA′:BB′}) = I(ρ_{A:B})`; and every such broadcast state is `(Θ_A ⊗ Θ_B)[ρ]` for some local
channels `Θ_A : A → AA′`, `Θ_B : B → BB′`. -/
theorem theorem_2 {a b : Type} [Fintype a] [DecidableEq a] [Nonempty a]
    [Fintype b] [DecidableEq b] [Nonempty b]
    (ρ : Matrix (a × b) (a × b) ℂ) (hρ : QAlgorithms.IsDensityMatrix ρ) :
    (IsLocallyBroadcastable ρ ↔
      ∃ σ : Matrix ((a × a) × (b × b)) ((a × a) × (b × b)) ℂ,
        IsBroadcastState ρ σ ∧ mutualInfo σ = mutualInfo ρ) ∧
    (∀ σ : Matrix ((a × a) × (b × b)) ((a × a) × (b × b)) ℂ,
      IsBroadcastState ρ σ → mutualInfo σ = mutualInfo ρ →
      ∃ (m n : ℕ) (K : Fin m → Matrix (a × a) a ℂ) (L : Fin n → Matrix (b × b) b ℂ),
        QAlgorithms.IsKrausFamily K ∧ QAlgorithms.IsKrausFamily L ∧ localApply K L ρ = σ) := by sorry

end NoLocalBroadcast.Broadcast
