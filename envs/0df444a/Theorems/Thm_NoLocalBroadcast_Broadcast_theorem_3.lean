-- Prove2me | Theorems.Thm_NoLocalBroadcast_Broadcast_theorem_3
-- name    : NoLocalBroadcast.Broadcast.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T09:35:28.380324+00:00
-- url     : https://prove2.me/theorems/412c52db-1dd9-4b81-a999-793bb895fd9e
-- title:
--   Theorem 3 with its converse (p. 3) — a bipartite state is locally broadcastable if and only if it is classical-classical
-- statement:
--   Let $\rho$ be a state of a finite-dimensional bipartite system $A\otimes B$, and let $A'$, $B'$ be copies of $A$, $B$. Then
--
--   $$\rho\text{ is locally broadcastable}\iff\rho\text{ is classical-classical.}$$
--
--   Here $\rho$ is locally broadcastable if there are channels $\Theta_A:A\to AA'$ and $\Theta_B:B\to BB'$ such that $\sigma=(\Theta_A\otimes\Theta_B)[\rho]$ satisfies $\operatorname{Tr}_{A'B'}\sigma=\operatorname{Tr}_{AB}\sigma=\rho$; and $\rho$ is classical-classical if $\rho=\sum_{ij}p_{ij}|i\rangle\langle i|\otimes|j\rangle\langle j|$ for orthonormal families $\{|i\rangle\}$ of $A$, $\{|j\rangle\}$ of $B$ and a joint probability distribution $p_{ij}$.
--
--   The direction "$\Rightarrow$" is Theorem 3: classical-classical states are the only states that can be locally broadcast. The direction "$\Leftarrow$" is the remark after Definition 6: a CC state is broadcast by cloning its biorthonormal eigenbasis locally. Even unentangled (separable) states that are not CC cannot be shared locally.
--
--   **Formalization Note** Channels are finite normalized Kraus families acting on $A$ alone and on $B$ alone; the two-copy state is indexed $((x,x'),(y,y'))$ and both reductions are required.
--
--   Differences from the source:
--   - generalization: Theorem 3: locally broadcastable ⟹ classical-classical → locally broadcastable ⟺ classical-classical; reason: the converse is the remark after Definition 6 (p. 3) and the abstract's 'if and only if'; the ⟹ half is Theorem 3
--   - encoding: finite-dimensional systems A, B and quantum states → nonempty finite index types a, b; states are positive semidefinite trace-one matrices (QAlgorithms.IsDensityMatrix), A the first factor of a × b; reason: the paper works in finite dimension throughout; same instances
--   - encoding: local maps / channels (trace-preserving completely positive, footnote [21]) → finite normalized Kraus families K : Fin m → Matrix a₁ a ℂ, L : Fin n → Matrix b₁ b ℂ; the local channel Λ_A ⊗ Γ_B has the Kraus operators K k ⊗ₖ L l (localApply); reason: in finite dimension these are exactly the CPTP maps and their tensor products; same instances
--   - encoding: the two-copy system (AA′)(BB′) with copies X = AB, Y = A′B′ → matrices indexed by ((x, x′), (y, y′)) ∈ (a × a) × (b × b); A′, B′ have the types of A, B; the cut AA′ : BB′ is the outer product; σ_X = traceCopies σ, σ_Y = traceOriginals σ; reason: Lean carrier convention; same operators
--   - encoding: classical-classical: two orthonormal sets {|i⟩}, {|j⟩} and a joint distribution p_ij with ρ = Σ_ij p_ij |i⟩⟨i| ⊗ |j⟩⟨j| → IsClassicalClassical: Orthonormal families e : Fin k → EuclideanSpace ℂ a, f : Fin l → EuclideanSpace ℂ b, p ≥ 0 with Σ p = 1, ρ = Σ_ij p_ij pureDensity (e i) ⊗ₖ pureDensity (f j); reason: an orthonormal set of a finite-dimensional space is a finite family; p may vanish, so families and sets give the same states
-- source:
--   Piani, Horodecki & Horodecki, No-local-broadcasting theorem for quantum correlations, arXiv:0707.0848v2, p. 3, Theorem 3 and the remark after Definition 6

import Mathlib
import Definitions.Def_NoLocalBroadcast_Broadcast_Model

namespace NoLocalBroadcast.Broadcast

open Matrix
open scoped Kronecker

/-- Theorem 3, p. 3, with its converse (remark after Definition 6, p. 3): a state of a finite
bipartite system is locally broadcastable if and only if it is classical-classical. -/
theorem theorem_3 {a b : Type} [Fintype a] [DecidableEq a] [Nonempty a]
    [Fintype b] [DecidableEq b] [Nonempty b]
    (ρ : Matrix (a × b) (a × b) ℂ) (hρ : QAlgorithms.IsDensityMatrix ρ) :
    IsLocallyBroadcastable ρ ↔ IsClassicalClassical ρ := by sorry

end NoLocalBroadcast.Broadcast
