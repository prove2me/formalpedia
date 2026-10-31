-- Prove2me | Theorems.Thm_FuchsThesis_Broadcast_eq_4_80
-- name    : FuchsThesis.Broadcast.eq_4_80
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:56:43.592373+00:00
-- url     : https://prove2.me/theorems/78bf8848-2a63-4ff2-920e-5f3b56b71397
-- title:
--   Eq. (4.80) — a broadcasting process preserves fidelity, $F(\tilde\rho_0,\tilde\rho_1) = F(\rho_0,\rho_1)$
-- statement:
--   Let $\rho_0,\rho_1$ be density operators of an $N$-dimensional system $A$, and let a process $E(X) = \mathrm{tr}_C\big(U(X\otimes\Upsilon)U^\dagger\big)$ (with $\Sigma$, $\Upsilon$ density operators of $B$ and $C$ and $U$ unitary on $ABC$) broadcast them: $\tilde\rho_s = E(\rho_s\otimes\Sigma)$ satisfies $\mathrm{tr}_A\tilde\rho_s = \rho_s$ and $\mathrm{tr}_B\tilde\rho_s = \rho_s$ for $s = 0,1$. Then
--
--   $$
--   F_A(\rho_0,\rho_1) = F(\tilde\rho_0,\tilde\rho_1) = F_B(\rho_0,\rho_1),
--   $$
--
--   where $F_A$ and $F_B$ both denote the fidelity $F(\rho_0,\rho_1)$ of (4.56); that is, $F(\tilde\rho_0,\tilde\rho_1) = F(\rho_0,\rho_1)$. This is the elementary constraint on every broadcasting process.
--
--   Differences from the source:
--   - reading: the chain $F_A(\rho_0,\rho_1) = F(\tilde\rho_0,\tilde\rho_1) = F_B(\rho_0,\rho_1)$ → the single equation $F(\tilde\rho_0,\tilde\rho_1) = F(\rho_0,\rho_1)$; reason: the source states that $F_A(\rho_0,\rho_1)$ and $F_B(\rho_0,\rho_1)$ denote "simply the fidelity $F(\rho_0,\rho_1)$" in two representations.
--   - encoding: auxiliary system $C$ → indices $\{0,\dots,k-1\}$; $N$-dimensional spaces → an arbitrary finite index type; reason: Lean convention; covers every finite-dimensional system.
--   - encoding: the trace $\mathrm{tr}\sqrt{\cdot}$ of (4.56) → the real part of the trace, square roots by the continuous functional calculus of the real square root; reason: Lean convention; on positive semidefinite arguments the trace is real and the square root is the positive one, so no instance changes.
-- source:
--   Fuchs, Distinguishability and Accessible Information in Quantum Theory, arXiv:quant-ph/9601020v1, §4.3, eq. (4.80), p.117 (PDF p.126)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_QuantumInformation
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_WildeQIT_partialTrace
import Definitions.Def_FuchsThesis_Broadcast_ancillaProcess

open scoped Kronecker

namespace FuchsThesis.Broadcast

/-- Fuchs, *Distinguishability and Accessible Information in Quantum Theory*,
arXiv:quant-ph/9601020v1, §4.3, eq. (4.80), p.117 (PDF p.126): the elementary constraint on
broadcasting. If a process `E` of the form (4.51) broadcasts `{ρ₀, ρ₁}`, i.e. `ρ̃ₛ = E(ρₛ ⊗ Σ)`
satisfies `tr_A ρ̃ₛ = ρₛ` and `tr_B ρ̃ₛ = ρₛ` for `s = 0, 1` (4.49), then
`F_A(ρ₀, ρ₁) = F(ρ̃₀, ρ̃₁) = F_B(ρ₀, ρ₁)`, where `F_A` and `F_B` are both the fidelity
`F(ρ₀, ρ₁)`; that is, `F(ρ̃₀, ρ̃₁) = F(ρ₀, ρ₁)`.

**Formalization Note.** `F` is `QAlgorithms.rootFidelity` = (4.56). `F_A(ρ₀, ρ₁)` and
`F_B(ρ₀, ρ₁)` are, in the source, `F(ρ₀, ρ₁)` written through an optimal POVM on `A` resp. `B`
("FA(ρ0, ρ1) denotes simply the fidelity F(ρ0, ρ1)", p.117), so both equalities of (4.80) are the
single equation `F(ρ̃₀, ρ̃₁) = F(ρ₀, ρ₁)`. Encoding as in `IsBroadcast`: `A`, `B` indexed by `n`,
`C` by `Fin k`, `tr_A`/`tr_B` the left/right partial traces, `E = ancillaProcess U Υ`. -/
theorem eq_4_80 {n : Type} [Fintype n] [DecidableEq n] {k : ℕ}
    (ρ0 ρ1 Sig : Matrix n n ℂ) (Ups : Matrix (Fin k) (Fin k) ℂ)
    (U : Matrix ((n × n) × Fin k) ((n × n) × Fin k) ℂ)
    (hρ0 : WildeQIT.IsDensityOperator ρ0) (hρ1 : WildeQIT.IsDensityOperator ρ1)
    (hSig : WildeQIT.IsDensityOperator Sig) (hUps : WildeQIT.IsDensityOperator Ups)
    (hU : U ∈ Matrix.unitaryGroup ((n × n) × Fin k) ℂ)
    (hbc : ∀ ρ ∈ ({ρ0, ρ1} : Set (Matrix n n ℂ)),
      WildeQIT.partialTraceLeft (ancillaProcess U Ups (ρ ⊗ₖ Sig)) = ρ ∧
      WildeQIT.partialTraceRight (ancillaProcess U Ups (ρ ⊗ₖ Sig)) = ρ) :
    QAlgorithms.rootFidelity (ancillaProcess U Ups (ρ0 ⊗ₖ Sig))
        (ancillaProcess U Ups (ρ1 ⊗ₖ Sig)) = QAlgorithms.rootFidelity ρ0 ρ1 := by sorry

end FuchsThesis.Broadcast
