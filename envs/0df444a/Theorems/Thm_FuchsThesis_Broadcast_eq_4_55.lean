-- Prove2me | Theorems.Thm_FuchsThesis_Broadcast_eq_4_55
-- name    : FuchsThesis.Broadcast.eq_4_55
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:55:26.224249+00:00
-- url     : https://prove2.me/theorems/d6a13fb9-835f-486f-ac96-b3a7b11a2b1e
-- title:
--   Eqs. (4.53)–(4.55) — commuting states can be broadcast without an auxiliary system
-- statement:
--   Let $\rho_0, \rho_1$ be density operators on an $N$-dimensional Hilbert space $A$ that commute, $\rho_0\rho_1 = \rho_1\rho_0$. Then there are a density operator $\Sigma$ on a second $N$-dimensional system $B$ and a unitary operator $U$ on $AB$ such that the states
--
--   $$
--   \tilde\rho_s = U(\rho_s\otimes\Sigma)U^\dagger, \qquad s = 0,1,
--   $$
--
--   satisfy
--
--   $$
--   \mathrm{tr}_A(\tilde\rho_s) = \rho_s \quad\text{and}\quad \mathrm{tr}_B(\tilde\rho_s) = \rho_s, \qquad s = 0,1 .
--   $$
--
--   In particular the set $\{\rho_0,\rho_1\}$ can be broadcast, and no auxiliary system is needed. This is the "if" half of the no-broadcasting theorem.
--
--   Differences from the source:
--   - reading: the source exhibits the choice $\Sigma = |1\rangle\langle1|$ and any unitary $U$ with $U|b\rangle|1\rangle = |b\rangle|b\rangle$ for a common eigenbasis $\{|b\rangle\}$, and concludes that $\tilde\rho_0,\tilde\rho_1$ satisfy (4.49) → there exist a density operator $\Sigma$ and a unitary $U$ on $AB$ with (4.49); reason: the paragraph's claim is that commuting states can be broadcast without an auxiliary system, and the specific choice is its proof.
--   - encoding: an $N$-dimensional Hilbert space → matrices indexed by an arbitrary finite type; reason: Lean convention, same instances up to relabelling.
-- source:
--   Fuchs, Distinguishability and Accessible Information in Quantum Theory, arXiv:quant-ph/9601020v1, §4.3, eqs. (4.53)–(4.55), p.114 (PDF p.123)

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_WildeQIT_partialTrace

open scoped Kronecker Matrix

namespace FuchsThesis.Broadcast

/-- Fuchs, *Distinguishability and Accessible Information in Quantum Theory*,
arXiv:quant-ph/9601020v1, §4.3, eqs. (4.53)–(4.55), p.114 (PDF p.123): commuting states can be
broadcast without an auxiliary system. If the density operators `ρ₀, ρ₁` on `A` commute, there are
a standard state `Σ` of `B` and a unitary `U` on `AB` such that `ρ̃ₛ = U (ρₛ ⊗ Σ) U†` satisfies
`tr_A ρ̃ₛ = ρₛ` and `tr_B ρ̃ₛ = ρₛ` for `s = 0, 1` (4.49).

**Formalization Note.** `A`, `B` are indexed by the finite type `n`, `AB` by `n × n`; `tr_A` is
`WildeQIT.partialTraceLeft`, `tr_B` is `WildeQIT.partialTraceRight`. The source's choice
`Σ = |1⟩⟨1|` and `U|b⟩|1⟩ = |b⟩|b⟩` is the proof, not the statement. -/
theorem eq_4_55 {n : Type} [Fintype n] [DecidableEq n] (ρ0 ρ1 : Matrix n n ℂ)
    (hρ0 : WildeQIT.IsDensityOperator ρ0) (hρ1 : WildeQIT.IsDensityOperator ρ1)
    (hcomm : ρ0 * ρ1 = ρ1 * ρ0) :
    ∃ (Sig : Matrix n n ℂ) (U : Matrix (n × n) (n × n) ℂ),
      WildeQIT.IsDensityOperator Sig ∧ U ∈ Matrix.unitaryGroup (n × n) ℂ ∧
      ∀ ρ ∈ ({ρ0, ρ1} : Set (Matrix n n ℂ)),
        WildeQIT.partialTraceLeft (U * (ρ ⊗ₖ Sig) * Uᴴ) = ρ ∧
        WildeQIT.partialTraceRight (U * (ρ ⊗ₖ Sig) * Uᴴ) = ρ := by sorry

end FuchsThesis.Broadcast
