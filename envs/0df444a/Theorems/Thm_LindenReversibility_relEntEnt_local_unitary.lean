-- Prove2me | Theorems.Thm_LindenReversibility_relEntEnt_local_unitary
-- name    : LindenReversibility.relEntEnt_local_unitary
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T03:18:25.342245+00:00
-- url     : https://prove2.me/theorems/58069f31-1ccc-47ed-a2ed-578e6aed1431
-- title:
--   p.3 after (14): local unitaries leave $E_r(\rho^{BC})$ and $S(\rho^A)$ unchanged
-- statement:
--   1. Let $U$ and $V$ be unitaries on Bob's and Claire's systems and $\rho$ a density matrix on $\mathbb C^B\otimes\mathbb C^C$. Then
--   $$
--   E_r\big((U\otimes V)\,\rho\,(U\otimes V)^\dagger\big) = E_r(\rho).
--   $$
--   2. Let $W$ be a unitary on Alice's system and $\rho^A$ a density matrix on it. Then $S(W\rho^AW^\dagger) = S(\rho^A)$.
--
--   These are the two facts of the paragraph after (14): the outcome-dependent rotations do not change $S(\rho^A_k)$, and $E_r(\rho^{BC}_k)$ is unchanged "since the set of separable states is invariant under local unitary transformations". They turn (13) into (15).
--
--   Differences from the source:
--   - reading: the local Hilbert spaces of Alice, Bob and Claire "including ancilla's" (dimension not stated) → arbitrary finite index types A, B, C (B, C nonempty); reason: the paper works with density matrices, a min over separable states (11) and finitely many copies of finite-dimensional systems; arbitrary finite types cover any number of copies and any ancillas
--   - encoding: min over separable σ in (11) → infimum over separable σ; reason: the minimum is attained (compact separable set, lower semicontinuous relative entropy), so the values agree
--   - reading: (14) printed as U^B_k ⊗ U^C_k ρ^{BC}_k ⊗ (U^C_k)^†, which is not a well-formed expression → the map ρ ↦ (U^B_k ⊗ U^C_k) ρ (U^B_k ⊗ U^C_k)^† (the unitaries act on the joint pure state); reason: the printed display omits (U^B_k)^†; the sentence after it ("if σ^{BC} is separable, then so is U ⊗ V σ^{BC} U^† ⊗ V^†") fixes the intended map
-- source:
--   Linden, Popescu, Schumacher, Westmoreland, Reversibility of local transformations of multiparticle entanglement, arXiv:quant-ph/9912039v1, p.3, sentence after (14)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P56
import Definitions.Def_LindenReversibility_relEntEnt

open QAlgorithms (IsDensityMatrix)
open QAlgorithms.Papers.Independent.Information100.P56 (entropy)
open scoped Matrix ENNReal

namespace LindenReversibility

/-- Linden, Popescu, Schumacher, Westmoreland, arXiv:quant-ph/9912039v1, p.3, after (14): local
unitaries do not change the quantities of the bound. "These transformations do not change
S(ρ^A_k). E_r(ρ^{BC}_k) is also left unchanged by these transformations since the set of separable
states is invariant under local unitary transformations."

Clause 1: for unitaries `U` on Bob's and `V` on Claire's system and every state `ρ` of `B × C`,
`E_r((U ⊗ V) ρ (U ⊗ V)†) = E_r(ρ)`. Clause 2: for a unitary `W` on Alice's system and every state
`ρ_A`, `S(W ρ_A W†) = S(ρ_A)`.

**Formalization Note.** Unitaries are members of `Matrix.unitaryGroup`; `U ⊗ V` is
`Matrix.kronecker U V`. The map is the intended `ρ ↦ (U ⊗ V) ρ (U ⊗ V)†`; the printed (14) omits
`(U^B_k)†`. -/
theorem relEntEnt_local_unitary {A B C : Type*} [Fintype A] [DecidableEq A] [Fintype B]
    [DecidableEq B] [Nonempty B] [Fintype C] [DecidableEq C] [Nonempty C]
    (U : Matrix B B ℂ) (hU : U ∈ Matrix.unitaryGroup B ℂ)
    (V : Matrix C C ℂ) (hV : V ∈ Matrix.unitaryGroup C ℂ)
    (ρ : Matrix (B × C) (B × C) ℂ) (hρ : IsDensityMatrix ρ)
    (W : Matrix A A ℂ) (hW : W ∈ Matrix.unitaryGroup A ℂ)
    (ρA : Matrix A A ℂ) (hρA : IsDensityMatrix ρA) :
    relEntEnt (Matrix.kronecker U V * ρ * (Matrix.kronecker U V)ᴴ) = relEntEnt ρ ∧
      entropy (W * ρA * Wᴴ) = entropy ρA := by sorry

end LindenReversibility
