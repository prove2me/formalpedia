-- Prove2me | Theorems.Thm_FuchsThesis_Broadcast_eq_4_76
-- name    : FuchsThesis.Broadcast.eq_4_76
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:56:37.954739+00:00
-- url     : https://prove2.me/theorems/adc955f0-a950-4e01-913e-8b3a11605eb2
-- title:
--   Eq. (4.76) — fidelity cannot decrease under the partial trace over $A$
-- statement:
--   Let $\tilde\rho_0, \tilde\rho_1$ be positive operators on a composite system $AB$ of finite dimension. Then the fidelity of their reductions to $B$ is at least their fidelity:
--
--   $$
--   F\big(\mathrm{tr}_A\tilde\rho_0,\ \mathrm{tr}_A\tilde\rho_1\big) \ge F(\tilde\rho_0,\tilde\rho_1),
--   $$
--
--   where $F(\rho,\sigma) = \mathrm{tr}\sqrt{\rho^{1/2}\sigma\rho^{1/2}}$ is the fidelity (4.56).
--
--   In the source, $\tilde\rho_s$ are the outputs of a broadcasting process, so $\mathrm{tr}_A\tilde\rho_s = \rho_s$, and the left side is written as $F_B(\rho_0,\rho_1) = \sum_b \sqrt{\mathrm{tr}(\tilde\rho_0(1\otimes E_b))}\sqrt{\mathrm{tr}(\tilde\rho_1(1\otimes E_b))}$ for an optimal measurement $\{E_b\}$ of $\rho_0,\rho_1$, which equals $F(\rho_0,\rho_1)$. Together with the companion bound for $\mathrm{tr}_B$ (4.74) it shows that a partial trace cannot decrease fidelity.
--
--   Differences from the source:
--   - generalization: the outputs $\tilde\rho_s$ of a broadcasting process on two $N$-dimensional systems → any positive semidefinite operators on $AB$, with $A$ and $B$ of any finite dimensions; reason: the source derives the inequality as the general partial-trace property ("this demonstrates the said partial trace property"); broadcasting outputs are such operators, so it specializes to the source's.
--   - reading: $F_B(\rho_0,\rho_1)$, the optimal-POVM representation of $F(\rho_0,\rho_1)$ with $\rho_s = \mathrm{tr}_A\tilde\rho_s$ → $F(\mathrm{tr}_A\tilde\rho_0, \mathrm{tr}_A\tilde\rho_1)$; reason: the source says $F_B(\rho_0,\rho_1)$ "stands for" $F(\rho_0,\rho_1)$ in that representation.
--   - encoding: the trace $\mathrm{tr}\sqrt{\cdot}$ of (4.56) → the real part of the trace, square roots by the continuous functional calculus of the real square root; reason: Lean convention; on positive semidefinite arguments the trace is real and the square root is the positive one, so no instance changes.
-- source:
--   Fuchs, Distinguishability and Accessible Information in Quantum Theory, arXiv:quant-ph/9601020v1, §4.3, eqs. (4.75)–(4.76), p.117 (PDF p.126)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_QuantumInformation
import Definitions.Def_WildeQIT_partialTrace

open scoped ComplexOrder

namespace FuchsThesis.Broadcast

/-- Fuchs, *Distinguishability and Accessible Information in Quantum Theory*,
arXiv:quant-ph/9601020v1, §4.3, eqs. (4.75)–(4.76), p.117 (PDF p.126): fidelity cannot decrease
under the partial trace over `A`: for positive operators `ρ̃₀, ρ̃₁` on `AB`,
`F(tr_A ρ̃₀, tr_A ρ̃₁) ≥ F(ρ̃₀, ρ̃₁)`.

**Formalization Note.** `F` is `QAlgorithms.rootFidelity` = (4.56); `AB` is indexed by `a × b`
(first factor `A`), and `tr_A` is `WildeQIT.partialTraceLeft`. In the source `ρ̃ₛ` are the
broadcast states with `tr_A ρ̃ₛ = ρₛ`, and the left side is written through an optimal POVM for
`ρ₀, ρ₁`; the inequality is the general partial-trace property, stated here for every pair of
positive semidefinite operators on `AB` with `A`, `B` of any finite dimensions. -/
theorem eq_4_76 {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (ρt0 ρt1 : Matrix (a × b) (a × b) ℂ) (h0 : ρt0.PosSemidef) (h1 : ρt1.PosSemidef) :
    QAlgorithms.rootFidelity ρt0 ρt1 ≤
      QAlgorithms.rootFidelity (WildeQIT.partialTraceLeft ρt0) (WildeQIT.partialTraceLeft ρt1) := by sorry

end FuchsThesis.Broadcast
