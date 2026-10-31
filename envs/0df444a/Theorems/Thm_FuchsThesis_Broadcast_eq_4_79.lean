-- Prove2me | Theorems.Thm_FuchsThesis_Broadcast_eq_4_79
-- name    : FuchsThesis.Broadcast.eq_4_79
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:56:43.890315+00:00
-- url     : https://prove2.me/theorems/a645025e-63af-4b63-ba54-536644c1b788
-- title:
--   Eq. (4.79) — fidelity cannot decrease under a process $E$ of the form (4.51)
-- statement:
--   Let $\rho_0,\rho_1$ be density operators of an $N$-dimensional system $A$, $\Sigma$ a density operator of an $N$-dimensional system $B$, $\Upsilon$ a density operator of a finite-dimensional auxiliary system $C$, and $U$ a unitary operator on $ABC$. With $E(X) = \mathrm{tr}_C\big(U(X\otimes\Upsilon)U^\dagger\big)$,
--
--   $$
--   F(\rho_0,\rho_1) \le F\big(E(\rho_0\otimes\Sigma),\ E(\rho_1\otimes\Sigma)\big),
--   $$
--
--   where $F$ is the fidelity (4.56). This is the inequality "opposite" to (4.74) and (4.76): together they force equality for any broadcasting process.
--
--   Differences from the source:
--   - encoding: an auxiliary system $C$ → indices $\{0,\dots,k-1\}$ for a natural number $k$; $N$-dimensional spaces → an arbitrary finite index type; reason: Lean convention; covers every finite-dimensional system.
--   - encoding: the trace $\mathrm{tr}\sqrt{\cdot}$ of (4.56) → the real part of the trace, square roots by the continuous functional calculus of the real square root; reason: Lean convention; on positive semidefinite arguments the trace is real and the square root is the positive one, so no instance changes.
-- source:
--   Fuchs, Distinguishability and Accessible Information in Quantum Theory, arXiv:quant-ph/9601020v1, §4.3, eqs. (4.77)–(4.79), p.117 (PDF p.126)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_QuantumInformation
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_FuchsThesis_Broadcast_ancillaProcess

open scoped Kronecker

namespace FuchsThesis.Broadcast

/-- Fuchs, *Distinguishability and Accessible Information in Quantum Theory*,
arXiv:quant-ph/9601020v1, §4.3, eqs. (4.77)–(4.79), p.117 (PDF p.126): fidelity cannot decrease
under a process of the form (4.51): for density operators `ρ₀, ρ₁` of `A`, a standard state `Σ`
of `B`, a standard state `Υ` of an auxiliary system `C` and a unitary `U` on `ABC`,
`F(ρ₀, ρ₁) ≤ F(E(ρ₀ ⊗ Σ), E(ρ₁ ⊗ Σ))` with `E(X) = tr_C (U (X ⊗ Υ) U†)`.

**Formalization Note.** `F` is `QAlgorithms.rootFidelity` = (4.56). `A`, `B` are indexed by `n`,
`C` by `Fin k`, `ABC` by `(n × n) × Fin k`; `E` is `ancillaProcess U Υ`. -/
theorem eq_4_79 {n : Type} [Fintype n] [DecidableEq n] {k : ℕ}
    (ρ0 ρ1 Sig : Matrix n n ℂ) (Ups : Matrix (Fin k) (Fin k) ℂ)
    (U : Matrix ((n × n) × Fin k) ((n × n) × Fin k) ℂ)
    (hρ0 : WildeQIT.IsDensityOperator ρ0) (hρ1 : WildeQIT.IsDensityOperator ρ1)
    (hSig : WildeQIT.IsDensityOperator Sig) (hUps : WildeQIT.IsDensityOperator Ups)
    (hU : U ∈ Matrix.unitaryGroup ((n × n) × Fin k) ℂ) :
    QAlgorithms.rootFidelity ρ0 ρ1 ≤
      QAlgorithms.rootFidelity (ancillaProcess U Ups (ρ0 ⊗ₖ Sig))
        (ancillaProcess U Ups (ρ1 ⊗ₖ Sig)) := by sorry

end FuchsThesis.Broadcast
