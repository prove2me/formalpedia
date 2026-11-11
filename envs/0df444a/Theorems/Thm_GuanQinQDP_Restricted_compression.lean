-- Prove2me | Theorems.Thm_GuanQinQDP_Restricted_compression
-- name    : GuanQinQDP.Restricted.compression
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:42:28.975718+00:00
-- url     : https://prove2.me/theorems/367bc266-f9ca-4259-85a9-87980f9fbedd
-- title:
--   Lemma 3.2 — compression to a Schmidt support of dimension at most two
-- statement:
--   Let $A$ be a channel on $H_i\otimes H_{\bar\imath}$ whose changed register is a qubit, $H_i=\mathbb C^2$. The complement $H_{\bar\imath}$ and the output may have any finite dimension. Let $\gamma\ge1$, let $M$ be an event on the output, and let $B=A^\dagger(M)$ be its pullback. Then
--
--   $$\sup_{\rho\sim_i\sigma}\operatorname{Tr}[B(\rho-\gamma\sigma)]=\sup\Big\{\operatorname{Tr}[B(\rho-\gamma\sigma)] : \rho\sim_i\sigma,\ \rho,\sigma\text{ supported on }H_i\otimes S\text{ for some }S\subseteq H_{\bar\imath},\ \dim S\le2\Big\}.$$
--
--   Both suprema range over pairs of density operators. The subspace $S$ may depend on the pair.
--
--   This is the first of the three reductions behind the exact semidefinite characterization (Theorem 3.5). It shrinks the unchanged side of a neighboring pair to dimension at most two without losing any deficit.
--
--   Differences from the source:
--
--   - generalization: complement H_ī = ⊗_{j≠i} H_j of the other registers → arbitrary nonempty finite index type C (register i first, H_i ⊗ C); reason: §3 uses no tensor structure of the complement; a source channel becomes one on ℂ² ⊗ H_ī by the regrouping splitEquiv, so the statement specializes to it
--   - encoding: H_ī a (nonzero) finite-dimensional Hilbert space → [Nonempty C]; reason: excludes only the zero space, on which there are no states
--   - generalization: M an event of a measurement class → M any effect on the output; reason: every event is an effect; the lemma is about a fixed M
--   - encoding: supported on H_i ⊗ S, S ⊆ H_ī, dim S ≤ 2 → SupportedOn V ρ ∧ SupportedOn V σ for an isometry V : ℂ^s → H_ī with s ≤ 2 (P X P = X, P = I ⊗ VV†); reason: every subspace of dimension s is the range of such an isometry; for a positive operator P X P = X is support inclusion
--   - encoding: sup over neighboring pairs → sSup of a real set; reason: the set is nonempty (ρ = σ, any state) and bounded by |value| ≤ 1 + γ, so sSup is the supremum
--   - encoding: Tr[B(ρ − γσ)] → pairValue B ρ σ γ, the real part of the trace; reason: B and ρ − γσ are Hermitian, so the trace is real
-- source:
--   Ji Guan, Yecheng Qin, Parallel Composition of Quantum Differential Privacy: The Role of Measurement Restrictions, STOC 2027 submission #1640 (October 2026), source.pdf SHA-256 da23c8347251683a16df4c61de3fa1604211cdbf34d757a7a45feb0efd54c694, Lemma 3.2 (printed p. 16 / PDF p. 17), with the standing assumptions of §3 (printed p. 15 / PDF p. 16)

import Definitions.Def_GuanQinQDP_Restricted_Model
open QAlgorithms WildeQIT.EntBreaking
open scoped Matrix

namespace GuanQinQDP.Restricted

/-- Lemma 3.2 (Compression), Guan–Qin, STOC 2027 submission #1640, printed p. 16 / PDF p. 17.
Setting of §3 (printed p. 15 / PDF p. 16): `A` is an arbitrary channel on `H_i ⊗ H_ī` with
`H_i = ℂ²` (register `i` first) and output `ℂ^K`, both `H_ī` and the output of any finite
dimension, `γ ≥ 1`, and `B = A†(M)` for an event `M`. The supremum of `Tr[B(ρ − γσ)]` over all
neighboring pairs `ρ ∼ᵢ σ` equals the supremum over the neighboring pairs that are both
supported on `H_i ⊗ S` for a subspace `S = range V ⊆ H_ī` with `dim S ≤ 2` (`S` may depend on
the pair). -/
theorem compression {C K : Type} [Fintype C] [DecidableEq C] [Nonempty C] [Fintype K]
    [DecidableEq K] (A : Matrix (Qubit × C) (Qubit × C) ℂ →ₗ[ℂ] Matrix K K ℂ)
    (hA : IsQuantumChannel A) (γ : ℝ) (hγ : 1 ≤ γ) (M : Matrix K K ℂ) (hM : IsEffect M) :
    sSup {x | ∃ ρ σ : Matrix (Qubit × C) (Qubit × C) ℂ,
        IsDensityMatrix ρ ∧ IsDensityMatrix σ ∧ NeighborFirst ρ σ ∧
          x = pairValue (pullback A M) ρ σ γ} =
      sSup {x | ∃ ρ σ : Matrix (Qubit × C) (Qubit × C) ℂ,
        IsDensityMatrix ρ ∧ IsDensityMatrix σ ∧ NeighborFirst ρ σ ∧
          (∃ s : ℕ, s ≤ 2 ∧ ∃ V : Matrix C (Fin s) ℂ, Vᴴ * V = 1 ∧
            SupportedOn V ρ ∧ SupportedOn V σ) ∧
          x = pairValue (pullback A M) ρ σ γ} := by sorry

end GuanQinQDP.Restricted
