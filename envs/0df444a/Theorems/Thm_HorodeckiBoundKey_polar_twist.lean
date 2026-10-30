-- Prove2me | Theorems.Thm_HorodeckiBoundKey_polar_twist
-- name    : HorodeckiBoundKey.polar_twist
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T03:15:54.180733+00:00
-- url     : https://prove2.me/theorems/a8a70608-3625-4085-a5ab-c27598fba485
-- title:
--   Polar-decomposition twisting: $\mathrm{Tr}\,X'' = \|X\|_1$ and the key pair is close to a singlet
-- statement:
--   Let $\sigma$ be a state on $A B A' B'$ (key qubits $A,B$; finite shields $A',B'$) and let $X$ be its $\langle 00|\cdot|11\rangle$ block. There is a twisting $U = \sum_{i,j}|ij\rangle\langle ij|\otimes U_{ij}$ (each $U_{ij}$ a unitary on $A'B'$) such that $\sigma'' = U\sigma U^\dagger$ satisfies
--   1. $\mathrm{Tr}\,X'' = \|X\|_1$, where $X''$ is the $\langle 00|\cdot|11\rangle$ block of $\sigma''$;
--   2. $\langle\psi^+|\,\mathrm{Tr}_{A'B'}\sigma''\,|\psi^+\rangle \ge 2\|X\|_1$, where $\psi^+ = (|00\rangle+|11\rangle)/\sqrt2$.
--
--   In the paper this is applied to $\rho'$ of (12): since $\|X\|_1$ is close to $1/2$, after the twisting the key pair is close to a singlet, while by Lemma 1 Eve's states correlated with the key outcomes do not change.
--
--   **Formalization Note** The twisting is the published `Dependency50.P24.twist`; $|\psi^+\rangle\langle\psi^+|$ is `bellProjector 2`, and $\mathrm{Tr}_{A'B'}$ is `QAlgorithms.traceRight`.
--
--   Differences from the source:
--   - generalization: the state ρ′ of (12), whose corner norm is close to 1/2 → every state σ on A B A′ B′ with finite shields; reason: the polar-decomposition argument uses no property of ρ′; the statement specializes to ρ′
--   - reading: "after tracing out A′B′, the state is close to singlet" → ⟨ψ⁺|Tr_{A′B′} σ″|ψ⁺⟩ ≥ 2‖X‖₁; reason: the quantitative form of the sentence: a corner norm above 1/2 − ε gives singlet fidelity above 1 − 2ε
-- source:
--   Horodecki, Horodecki, Horodecki, Oppenheim, Secure key from bound entanglement, arXiv:quant-ph/0309110v2, p.3 ("by use of polar decomposition, one finds twisting operation after which trace of the block X is equal to its trace norm … after tracing out A′B′, the state is close to singlet")

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P24
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P42

open QAlgorithms QAlgorithms.Papers.Independent
open QAlgorithms.Papers.Independent.Information100.P21 (Op)
open scoped Matrix ComplexOrder ENNReal
open QAlgorithms.Papers.Independent.Dependency50.P24 (Key keyBlock twist)
open QAlgorithms.Papers.Independent.Information100.P04 (bellProjector)

namespace HorodeckiBoundKey

/-- Horodecki, Horodecki, Horodecki, Oppenheim, arXiv:quant-ph/0309110v2, p.3: "Since trace norm
of the off-diagonal block (12) of the state is close to 1/2, by use of polar decomposition, one
finds twisting operation after which trace of the block X is equal to its trace norm. … Now
however, after tracing out A′B′, the state is close to singlet."

For every state `σ` on `A B A′ B′` (key qubits `A B`, shields `A′ B′`) there is a twisting
`U = ∑_{ij} |ij⟩⟨ij| ⊗ U_{ij}` such that the twisted state `σ″ = U σ U†` satisfies
1. `Tr X″ = ‖X‖₁`, where `X` and `X″` are the `⟨00|·|11⟩` blocks of `σ` and `σ″`;
2. `⟨ψ⁺| Tr_{A′B′} σ″ |ψ⁺⟩ ≥ 2 ‖X‖₁`, with `ψ⁺ = (|00⟩ + |11⟩)/√2`.

**Formalization Note.** Twisting is `Dependency50.P24.twist` (conjugation by the controlled
unitary of (2)); the trace norm is `QAlgorithms.traceNorm`. Clause 2 is the quantitative form
of "close to singlet" that the sentence leaves implicit: with clause 1 the singlet overlap is
`(Tr σ₀₀,₀₀ + Tr σ₁₁,₁₁)/2 + ‖X‖₁`, and `‖X‖₁ ≤ (Tr σ₀₀,₀₀ + Tr σ₁₁,₁₁)/2` for a state, so a corner
norm `> 1/2 − ε` gives singlet fidelity `> 1 − 2ε`. `|ψ⁺⟩⟨ψ⁺|` is `bellProjector 2` and
`Tr_{A′B′}` is `QAlgorithms.traceRight`. -/
theorem polar_twist {S T : Type*} [Fintype S] [DecidableEq S] [Fintype T] [DecidableEq T]
    (σ : Op (Key 2 × (S × T))) (hσ : IsDensityMatrix σ) :
    ∃ U : Key 2 → Matrix.unitaryGroup (S × T) ℂ,
      (keyBlock (twist U σ) (0,0) (1,1)).trace = (traceNorm (keyBlock σ (0,0) (1,1)) : ℂ) ∧
      2 * traceNorm (keyBlock σ (0,0) (1,1)) ≤
        (bellProjector 2 * traceRight (twist U σ)).trace.re := by sorry

end HorodeckiBoundKey
