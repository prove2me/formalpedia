-- Prove2me | Theorems.Thm_NoLocalBroadcast_Broadcast_display_1_equality
-- name    : NoLocalBroadcast.Broadcast.display_1_equality
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:35:38.792271+00:00
-- url     : https://prove2.me/theorems/607431ff-cae9-4856-98f6-b167b699e835
-- title:
--   Equality in (1) (pp. 3–4) — equality forces ρ^ij_A′ to depend only on i and ρ^ij_B′ only on j on the support of p
-- statement:
--   In the setting of display (1) — finite sets $I$, $J$, a probability distribution $\{p_{ij}\}$ on $I\times J$, states $\rho^{ij}$ of $A'B'$ and $\tilde\sigma=\sum_{ij}p_{ij}|i\rangle\langle i|_A\otimes|j\rangle\langle j|_B\otimes\rho^{ij}_{A'B'}$ — suppose that
--
--   $$I(\tilde\sigma)=I(\{p_{ij}\})+\sum_{ij}p_{ij}\,I(\rho^{ij}_{A'B'}).$$
--
--   Then
--
--   1. $\rho^{ij}_{A'}=\rho^{ij'}_{A'}$ whenever $p_{ij}>0$ and $p_{ij'}>0$;
--   2. $\rho^{ij}_{B'}=\rho^{i'j}_{B'}$ whenever $p_{ij}>0$ and $p_{i'j}>0$.
--
--   That is, on the support of $p$ the reduction $\rho^{ij}_{A'}$ depends only on $i$ and $\rho^{ij}_{B'}$ only on $j$, which is the paper's "$\rho^{ij}_{A'}=\rho^i_{A'}$ and $\rho^{ij}_{B'}=\rho^j_{B'}$". It is the step of Theorem 3's proof that shows $\tilde\sigma$ to be classical-classical.
--
--   **Formalization Note** The conventions are those of display (1); $\rho^{ij}_{A'}$ is `traceRight (ρij (i,j))` and $\rho^{ij}_{B'}$ is `traceLeft (ρij (i,j))`.
--
--   Differences from the source:
--   - generalization: the specific σ̃ of the proof of Theorem 3, with equality I(σ̃) = I_CC(ρ) + Σ p_ij I(ρ^ij) → every σ̃ of the form Σ_ij p_ij |i⟩⟨i| ⊗ |j⟩⟨j| ⊗ ρ^ij, with equality I(σ̃) = I({p_ij}) + Σ p_ij I(ρ^ij); reason: in the proof I({p_ij}) = I_CC(ρ), so the proof's equality is an instance
--   - reading: ρ^ij_A′ = ρ^i_A′ and ρ^ij_B′ = ρ^j_B′ (ρ^i_A′, ρ^j_B′ not defined) → on the support of p, ρ^ij_A′ does not depend on j and ρ^ij_B′ does not depend on i; reason: the only meaning of the notation; off the support ρ^ij does not enter σ̃
--   - encoding: ρ^ij defined where p_ij > 0 → ρ^ij a state for every (i, j); reason: the conclusion only concerns pairs with p_ij > 0
--   - encoding: log of unspecified base in S(ρ) = −Tr ρ log ρ → QAlgorithms.vnEntropy, base 2; reason: every statement here is invariant under the base of the logarithm
--   - encoding: σ̃ = Σ_ij p_ij |i_A j_B⟩⟨i_A j_B| ⊗ ρ^ij_{A′B′} on registers A, B with orthonormal states and quantum systems A′, B′, cut AA′ : BB′ → flaggedState p ρij on (ι × a′) × (κ × b′) for finite register types ι, κ and nonempty finite a′, b′, registers the computational bases of ι, κ; ρ^ij_{A′} = traceRight (ρij ij), ρ^ij_{B′} = traceLeft (ρij ij); reason: any orthonormal register gives a unitarily equivalent state with the same entropies; empty ι or κ is excluded by Σ p = 1; same instances
-- source:
--   Piani, Horodecki & Horodecki, No-local-broadcasting theorem for quantum correlations, arXiv:0707.0848v2, pp. 3–4, equality in (1), proof of Theorem 3

import Mathlib
import Definitions.Def_NoLocalBroadcast_Broadcast_Model

namespace NoLocalBroadcast.Broadcast

open Matrix
open scoped Kronecker

/-- Equality in (1), pp. 3–4: if `I(σ̃) = I({p_ij}) + Σ_{ij} p_{ij} I(ρ^{ij})`, then on the support
of `p` the reduction `ρ^{ij}_{A′}` does not depend on `j` and `ρ^{ij}_{B′}` does not depend on `i`. -/
theorem display_1_equality {ι κ a' b' : Type} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] [Fintype a'] [DecidableEq a'] [Nonempty a'] [Fintype b'] [DecidableEq b']
    [Nonempty b']
    (p : ι × κ → ℝ) (hp0 : ∀ ij, 0 ≤ p ij) (hp1 : ∑ ij, p ij = 1)
    (ρij : ι × κ → Matrix (a' × b') (a' × b') ℂ)
    (hρij : ∀ ij, QAlgorithms.IsDensityMatrix (ρij ij))
    (heq : mutualInfo (flaggedState p ρij) =
      mutualInfo (Matrix.diagonal fun ij => (p ij : ℂ)) + ∑ ij, p ij * mutualInfo (ρij ij)) :
    (∀ i j j', 0 < p (i, j) → 0 < p (i, j') →
      QAlgorithms.traceRight (ρij (i, j)) = QAlgorithms.traceRight (ρij (i, j'))) ∧
    (∀ i i' j, 0 < p (i, j) → 0 < p (i', j) →
      QAlgorithms.traceLeft (ρij (i, j)) = QAlgorithms.traceLeft (ρij (i', j))) := by sorry

end NoLocalBroadcast.Broadcast
