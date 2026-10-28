-- Prove2me | Theorems.Thm_NoLocalBroadcast_Broadcast_cc_locally_broadcastable
-- name    : NoLocalBroadcast.Broadcast.cc_locally_broadcastable
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:35:20.714099+00:00
-- url     : https://prove2.me/theorems/1045c0d2-6378-4293-b1dd-38f03a3847c2
-- title:
--   Remark after Definition 6 (p. 3) — every classical-classical state is locally broadcastable
-- statement:
--   Let $\rho$ be a classical-classical state of a finite-dimensional bipartite system $A\otimes B$: $\rho=\sum_{ij}p_{ij}|i\rangle\langle i|\otimes|j\rangle\langle j|$ for orthonormal families $\{|i\rangle\}$ of $A$, $\{|j\rangle\}$ of $B$ and a joint distribution $p_{ij}$. Then $\rho$ is locally broadcastable: there are channels $\Theta_A:A\to AA'$ and $\Theta_B:B\to BB'$ such that
--
--   $$\operatorname{Tr}_{A'B'}\big[(\Theta_A\otimes\Theta_B)[\rho]\big]=\operatorname{Tr}_{AB}\big[(\Theta_A\otimes\Theta_B)[\rho]\big]=\rho .$$
--
--   This is the converse of Theorem 3; together they characterize the locally broadcastable states.
--
--   **Formalization Note** No separate density-matrix hypothesis is needed: a classical-classical matrix is a state.
--
--   Differences from the source:
--   - encoding: finite-dimensional systems A, B and quantum states → nonempty finite index types a, b; states are positive semidefinite trace-one matrices (QAlgorithms.IsDensityMatrix), A the first factor of a × b; reason: the paper works in finite dimension throughout; same instances
--   - encoding: local maps / channels (trace-preserving completely positive, footnote [21]) → finite normalized Kraus families K : Fin m → Matrix a₁ a ℂ, L : Fin n → Matrix b₁ b ℂ; the local channel Λ_A ⊗ Γ_B has the Kraus operators K k ⊗ₖ L l (localApply); reason: in finite dimension these are exactly the CPTP maps and their tensor products; same instances
--   - encoding: the two-copy system (AA′)(BB′) with copies X = AB, Y = A′B′ → matrices indexed by ((x, x′), (y, y′)) ∈ (a × a) × (b × b); A′, B′ have the types of A, B; the cut AA′ : BB′ is the outer product; σ_X = traceCopies σ, σ_Y = traceOriginals σ; reason: Lean carrier convention; same operators
--   - encoding: classical-classical: two orthonormal sets {|i⟩}, {|j⟩} and a joint distribution p_ij with ρ = Σ_ij p_ij |i⟩⟨i| ⊗ |j⟩⟨j| → IsClassicalClassical: Orthonormal families e : Fin k → EuclideanSpace ℂ a, f : Fin l → EuclideanSpace ℂ b, p ≥ 0 with Σ p = 1, ρ = Σ_ij p_ij pureDensity (e i) ⊗ₖ pureDensity (f j); reason: an orthonormal set of a finite-dimensional space is a finite family; p may vanish, so families and sets give the same states
-- source:
--   Piani, Horodecki & Horodecki, No-local-broadcasting theorem for quantum correlations, arXiv:0707.0848v2, p. 3, remark after Definition 6

import Mathlib
import Definitions.Def_NoLocalBroadcast_Broadcast_Model

namespace NoLocalBroadcast.Broadcast

open Matrix
open scoped Kronecker

/-- Remark after Definition 6, p. 3: every classical-classical state is locally broadcastable. -/
theorem cc_locally_broadcastable {a b : Type} [Fintype a] [DecidableEq a] [Nonempty a]
    [Fintype b] [DecidableEq b] [Nonempty b]
    (ρ : Matrix (a × b) (a × b) ℂ) (hcc : IsClassicalClassical ρ) :
    IsLocallyBroadcastable ρ := by sorry

end NoLocalBroadcast.Broadcast
