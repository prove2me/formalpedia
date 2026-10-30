-- Prove2me | Theorems.Thm_LindenReversibility_eq_21
-- name    : LindenReversibility.eq_21
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T03:18:19.347512+00:00
-- url     : https://prove2.me/theorems/f524d26e-84c3-4e0a-8ae4-4606417e8f18
-- title:
--   Eq. (21): $E_r$ does not increase on average under a local measurement and local unitaries
-- statement:
--   Let $\rho$ be a density matrix on $\mathbb C^B\otimes\mathbb C^C$.
--
--   1. Bob measures with a complete family $K_1,\dots,K_n$ on his system, the outcome is broadcast, and Bob and Claire apply unitaries $U_k$, $V_k$ depending on it. Let $M_k = (U_k\otimes V_k)(K_k\otimes I)\rho(K_k\otimes I)^\dagger(U_k\otimes V_k)^\dagger$, $p_k = \operatorname{Tr}M_k$ and $\tilde\rho_k = M_k/p_k$ (and $\tilde\rho_k = 0$ if $p_k = 0$). Then
--   $$
--   E_r(\rho) \ge \sum_k p_k E_r(\tilde\rho_k).
--   $$
--   2. The same holds when Claire measures, with $(I\otimes K_k)$ in place of $(K_k\otimes I)$.
--
--   This is the monotonicity of the relative entropy of entanglement under local operations and classical communication, which the paper quotes from Vedral and Plenio [4] and applies to $\rho = \rho^{BC}$, the (mixed) reduced state of the joint pure state, in a step by Bob.
--
--   Differences from the source:
--   - reading: the local Hilbert spaces of Alice, Bob and Claire "including ancilla's" (dimension not stated) → arbitrary finite nonempty index types B, C (Alice's system does not enter this statement); reason: the paper works with density matrices, a min over separable states (11) and finitely many copies of finite-dimensional systems; arbitrary finite types cover any number of copies and any ancillas
--   - generalization: a local measurement with spectral projectors P_k (followed by outcome-dependent unitaries) → any finite family K_k of operators on the acting party's system with sum_k K_k^dagger K_k = 1; reason: spectral projectors, projectors followed by unitaries, and single unitaries are such families, so the statement specializes to the paper's; the paper's argument uses only the completeness relation
--   - encoding: min over separable σ in (11) → infimum over separable σ; reason: the minimum is attained (compact separable set, lower semicontinuous relative entropy), so the values agree
--   - encoding: outcome probabilities p_k and normalized post-measurement states → p_k = Re Tr M_k and ρ̃_k = M_k / p_k, with ρ̃_k = 0 when p_k = 0; reason: a zero-probability outcome has weight 0 and drops out of the sum, as in the paper
--   - generalization: (21) for a measurement by Bob → clauses for Bob and for Claire; reason: Claire's clauses are Bob's with B and C exchanged; the paper's argument covers any party ("(15) is true for any step"); the Bob clauses are the source's statement
--   - generalization: ρ^{BC}, the reduced state of the joint pure state in the current branch → any density matrix ρ on B × C; reason: every density matrix on B × C is such a reduced state (purify it on a large enough A), and the paper's instance is one of them
-- source:
--   Linden, Popescu, Schumacher, Westmoreland, Reversibility of local transformations of multiparticle entanglement, arXiv:quant-ph/9912039v1, eq. (21), p.3

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_LindenReversibility_IsKrausFamily
import Definitions.Def_LindenReversibility_relEntEnt

open QAlgorithms (IsDensityMatrix)
open scoped Matrix ENNReal

namespace LindenReversibility

/-- Linden, Popescu, Schumacher, Westmoreland, arXiv:quant-ph/9912039v1, eq. (21), p.3: the
relative entropy of entanglement does not increase on average under local operations and
classical communication: when Bob measures, communicates the outcome `k`, and Bob and Claire
apply unitaries depending on it, `E_r(ρ^{BC}) ≥ ∑_k p_k E_r(ρ̃^{BC}_k)`. The same holds for a
measurement by Claire. (The paper cites this to Vedral–Plenio [4].)

Clause 1: Bob measures with a complete family `K_k` on `B`; clause 2: Claire measures with a
complete family on `C`. In both, `U_k`, `V_k` are the outcome-dependent unitaries of Bob and
Claire.

**Formalization Note.** `ρ` is any state of `B × C` (in the paper, the mixed reduced state
`Tr_A` of a pure tripartite state). With `M_k = (U_k ⊗ V_k)(K_k ⊗ 1) ρ (K_k ⊗ 1)† (U_k ⊗ V_k)†`
(resp. `1 ⊗ K_k`), `p_k = Re Tr M_k` and `ρ̃_k = M_k / p_k`; a term with `p_k = 0` has
`ρ̃_k = 0` and weight `0`, so it drops out. Values in `ℝ≥0∞`. -/
theorem eq_21 {B C : Type*} [Fintype B] [DecidableEq B] [Nonempty B] [Fintype C]
    [DecidableEq C] [Nonempty C] (ρ : Matrix (B × C) (B × C) ℂ) (hρ : IsDensityMatrix ρ) :
    (∀ (n : ℕ) (K : Fin n → Matrix B B ℂ) (U : Fin n → Matrix B B ℂ)
        (V : Fin n → Matrix C C ℂ), IsKrausFamily K →
        (∀ k, U k ∈ Matrix.unitaryGroup B ℂ) → (∀ k, V k ∈ Matrix.unitaryGroup C ℂ) →
      let M : Fin n → Matrix (B × C) (B × C) ℂ := fun k =>
        Matrix.kronecker (U k) (V k) * Matrix.kronecker (K k) (1 : Matrix C C ℂ) * ρ *
          (Matrix.kronecker (K k) (1 : Matrix C C ℂ))ᴴ * (Matrix.kronecker (U k) (V k))ᴴ
      ∑ k, ENNReal.ofReal (M k).trace.re * relEntEnt (((M k).trace.re)⁻¹ • M k) ≤
        relEntEnt ρ) ∧
    (∀ (n : ℕ) (K : Fin n → Matrix C C ℂ) (U : Fin n → Matrix B B ℂ)
        (V : Fin n → Matrix C C ℂ), IsKrausFamily K →
        (∀ k, U k ∈ Matrix.unitaryGroup B ℂ) → (∀ k, V k ∈ Matrix.unitaryGroup C ℂ) →
      let M : Fin n → Matrix (B × C) (B × C) ℂ := fun k =>
        Matrix.kronecker (U k) (V k) * Matrix.kronecker (1 : Matrix B B ℂ) (K k) * ρ *
          (Matrix.kronecker (1 : Matrix B B ℂ) (K k))ᴴ * (Matrix.kronecker (U k) (V k))ᴴ
      ∑ k, ENNReal.ofReal (M k).trace.re * relEntEnt (((M k).trace.re)⁻¹ • M k) ≤
        relEntEnt ρ) := by sorry

end LindenReversibility
