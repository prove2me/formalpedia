-- Prove2me | Theorems.Thm_NoLocalBroadcast_Broadcast_display_1
-- name    : NoLocalBroadcast.Broadcast.display_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:35:29.7266+00:00
-- url     : https://prove2.me/theorems/628aa7fa-1940-48c2-ba21-d9b62700eb5f
-- title:
--   Display (1) (p. 3) — I(σ̃) = I({p_ij}) + Σ p_i^A S(τ^i) + Σ p_j^B S(τ^j) − Σ p_ij S(ρ^ij) ≥ I({p_ij}) + Σ p_ij I(ρ^ij)
-- statement:
--   Let $I$, $J$ be finite sets, $\{p_{ij}\}$ a probability distribution on $I\times J$, and $\rho^{ij}$ states of a finite-dimensional bipartite system $A'B'$. Let
--
--   $$\tilde\sigma=\sum_{ij}p_{ij}\,|i\rangle\langle i|_A\otimes|j\rangle\langle j|_B\otimes\rho^{ij}_{A'B'},$$
--
--   regarded as a state across the cut $AA':BB'$. Write $p_i^A=\sum_jp_{ij}$, $p_j^B=\sum_ip_{ij}$, $\tau^i_{A'}=\sum_j\frac{p_{ij}}{p_i^A}\rho^{ij}_{A'}$ and $\tau^j_{B'}=\sum_i\frac{p_{ij}}{p_j^B}\rho^{ij}_{B'}$, and let $I(\{p_{ij}\})$ be the classical mutual information of $\{p_{ij}\}$. Then
--
--   $$I(\tilde\sigma)=I(\{p_{ij}\})+\sum_ip_i^AS(\tau^i_{A'})+\sum_jp_j^BS(\tau^j_{B'})-\sum_{ij}p_{ij}S(\rho^{ij}_{A'B'})\ \ge\ I(\{p_{ij}\})+\sum_{ij}p_{ij}I(\rho^{ij}_{A'B'}).$$
--
--   In the proof of Theorem 3, $\tilde\sigma$ is obtained by measuring $A$ and $B$ of a broadcast state with measurements optimal for $I_{CC}(\rho)$, so that $I(\{p_{ij}\})=I_{CC}(\rho)$ and the lower bound is the printed $I_{CC}(\rho)+\sum_{ij}p_{ij}I(\rho^{ij})$.
--
--   **Formalization Note** $\tilde\sigma$ is `flaggedState p ρij`, indexed $((i,x'),(j,y'))$. $I(\{p_{ij}\})$ is the quantum mutual information of the diagonal matrix of $p$ on $I\times J$, which equals the classical mutual information. When $p_i^A=0$ the division gives $\tau^i_{A'}=0$, whose entropy is $0$, and the term is multiplied by $p_i^A=0$ anyway; similarly for $B$. The $\rho^{ij}$ are states for every $(i,j)$; those with $p_{ij}=0$ do not enter $\tilde\sigma$.
--
--   Differences from the source:
--   - generalization: the specific σ̃ = (M_A ⊗ N_B)[σ] of the proof of Theorem 3 → every σ̃ = Σ_ij p_ij |i⟩⟨i| ⊗ |j⟩⟨j| ⊗ ρ^ij for finite registers, a probability distribution p and states ρ^ij; reason: the proof's σ̃ is of this form, so the statement specializes to it
--   - generalization: lower bound I_CC(ρ) + Σ_ij p_ij I(ρ^ij) → lower bound I({p_ij}) + Σ_ij p_ij I(ρ^ij); reason: the paper replaces I({p_ij}) by I_CC(ρ) using I({p_ij}) = I_CC(ρ) for its optimal measurements; in that context the two bounds coincide, and the Lean bound holds for every σ̃
--   - encoding: classical mutual information I({p_ij}) = H(p^A) + H(p^B) − H(p) → mutualInfo of Matrix.diagonal p on ι × κ; reason: the von Neumann entropies of diagonal matrices are the Shannon entropies of their diagonals; same number
--   - encoding: ρ^ij defined where p_ij > 0; τ^i with p_i^A in the denominator → ρ^ij a state for every (i, j); real division with x / 0 = 0; reason: terms with p_ij = 0 or p_i^A = 0 carry weight 0 on both sides; same values
--   - encoding: log of unspecified base in S(ρ) = −Tr ρ log ρ → QAlgorithms.vnEntropy, base 2; reason: every statement here is invariant under the base of the logarithm
--   - encoding: σ̃ = Σ_ij p_ij |i_A j_B⟩⟨i_A j_B| ⊗ ρ^ij_{A′B′} on registers A, B with orthonormal states and quantum systems A′, B′, cut AA′ : BB′ → flaggedState p ρij on (ι × a′) × (κ × b′) for finite register types ι, κ and nonempty finite a′, b′, registers the computational bases of ι, κ; ρ^ij_{A′} = traceRight (ρij ij), ρ^ij_{B′} = traceLeft (ρij ij); reason: any orthonormal register gives a unitarily equivalent state with the same entropies; empty ι or κ is excluded by Σ p = 1; same instances
-- source:
--   Piani, Horodecki & Horodecki, No-local-broadcasting theorem for quantum correlations, arXiv:0707.0848v2, p. 3, display (1) in the proof of Theorem 3

import Mathlib
import Definitions.Def_NoLocalBroadcast_Broadcast_Model

namespace NoLocalBroadcast.Broadcast

open Matrix
open scoped Kronecker

/-- Display (1), p. 3: for `σ̃ = Σ_{ij} p_{ij} |i⟩⟨i| ⊗ |j⟩⟨j| ⊗ ρ^{ij}` (cut `AA′ : BB′`),
`I(σ̃) = I({p_ij}) + Σ_i p_i^A S(τ^i_{A′}) + Σ_j p_j^B S(τ^j_{B′}) − Σ_{ij} p_{ij} S(ρ^{ij})`
and `I(σ̃) ≥ I({p_ij}) + Σ_{ij} p_{ij} I(ρ^{ij})`, where `I({p_ij})` is the mutual information
of the diagonal state of `p`. -/
theorem display_1 {ι κ a' b' : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    [Fintype a'] [DecidableEq a'] [Nonempty a'] [Fintype b'] [DecidableEq b'] [Nonempty b']
    (p : ι × κ → ℝ) (hp0 : ∀ ij, 0 ≤ p ij) (hp1 : ∑ ij, p ij = 1)
    (ρij : ι × κ → Matrix (a' × b') (a' × b') ℂ)
    (hρij : ∀ ij, QAlgorithms.IsDensityMatrix (ρij ij)) :
    mutualInfo (flaggedState p ρij) =
        mutualInfo (Matrix.diagonal fun ij => (p ij : ℂ))
          + ∑ i, (∑ j, p (i, j)) * QAlgorithms.vnEntropy
              (∑ j, ((p (i, j) / ∑ j', p (i, j') : ℝ) : ℂ) • QAlgorithms.traceRight (ρij (i, j)))
          + ∑ j, (∑ i, p (i, j)) * QAlgorithms.vnEntropy
              (∑ i, ((p (i, j) / ∑ i', p (i', j) : ℝ) : ℂ) • QAlgorithms.traceLeft (ρij (i, j)))
          - ∑ ij, p ij * QAlgorithms.vnEntropy (ρij ij) ∧
    mutualInfo (Matrix.diagonal fun ij => (p ij : ℂ)) + ∑ ij, p ij * mutualInfo (ρij ij)
      ≤ mutualInfo (flaggedState p ρij) := by sorry

end NoLocalBroadcast.Broadcast
