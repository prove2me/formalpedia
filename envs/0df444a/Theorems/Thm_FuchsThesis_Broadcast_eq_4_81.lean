-- Prove2me | Theorems.Thm_FuchsThesis_Broadcast_eq_4_81
-- name    : FuchsThesis.Broadcast.eq_4_81
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:57:33.512606+00:00
-- url     : https://prove2.me/theorems/a478c284-8a61-43fe-88ef-4dd1ca136aa1
-- title:
--   Eq. (4.81) — clonable states have $F(\rho_0,\rho_1) = F(\rho_0,\rho_1)^2$, so $F \in \{0, 1\}$, i.e. identical or orthogonal
-- statement:
--   Let $\rho_0,\rho_1$ be density operators on an $N$-dimensional system, and suppose $\{\rho_0,\rho_1\}$ is clonable: some physical process $E$ (with a standard state $\Sigma$ of $B$) satisfies $E(\rho_s\otimes\Sigma) = \rho_s\otimes\rho_s$ for $s = 0,1$. Then
--
--   $$
--   F(\rho_0,\rho_1) = F(\rho_0\otimes\rho_0,\ \rho_1\otimes\rho_1) = \big(F(\rho_0,\rho_1)\big)^2,
--   $$
--
--   which means that $F(\rho_0,\rho_1) = 1$ or $0$, i.e., $\rho_0$ and $\rho_1$ are identical or orthogonal: $\rho_0 = \rho_1$ or $\rho_0\rho_1 = 0$. There can be no cloning for density operators with nontrivial fidelity.
--
--   Differences from the source:
--   - encoding: "orthogonal" → $\rho_0\rho_1 = 0$; reason: the source's own meaning of orthogonal states, eq. (4.52).
--   - encoding: an auxiliary system $C$ → indices $\{0,\dots,k-1\}$ for some natural number $k$; $N$-dimensional spaces → an arbitrary finite index type; reason: Lean convention; covers every finite dimension and every finite-dimensional auxiliary system.
--   - encoding: the trace $\mathrm{tr}\sqrt{\cdot}$ of (4.56) → the real part of the trace, square roots by the continuous functional calculus of the real square root; reason: Lean convention; on positive semidefinite arguments the trace is real and the square root is the positive one, so no instance changes.
-- source:
--   Fuchs, Distinguishability and Accessible Information in Quantum Theory, arXiv:quant-ph/9601020v1, §4.3, eq. (4.81), p.117 (PDF p.126)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_QuantumInformation
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_FuchsThesis_Broadcast_IsClone

open scoped Kronecker

namespace FuchsThesis.Broadcast

/-- Fuchs, *Distinguishability and Accessible Information in Quantum Theory*,
arXiv:quant-ph/9601020v1, §4.3, eq. (4.81), p.117 (PDF p.126): if `{ρ₀, ρ₁}` is clonable, then
`F(ρ₀, ρ₁) = F(ρ₀ ⊗ ρ₀, ρ₁ ⊗ ρ₁) = (F(ρ₀, ρ₁))²`, which means that `F(ρ₀, ρ₁) = 1` or `0`,
i.e., `ρ₀` and `ρ₁` are identical or orthogonal (`ρ₀ ρ₁ = 0`, (4.52)).

**Formalization Note.** `F` is `QAlgorithms.rootFidelity` = (4.56); `ρ ⊗ ρ` is the Kronecker
product indexed by `n × n`; clonability is `IsClone`. -/
theorem eq_4_81 {n : Type} [Fintype n] [DecidableEq n] (ρ0 ρ1 : Matrix n n ℂ)
    (hρ0 : WildeQIT.IsDensityOperator ρ0) (hρ1 : WildeQIT.IsDensityOperator ρ1)
    (hclone : IsClone ρ0 ρ1) :
    QAlgorithms.rootFidelity ρ0 ρ1 = QAlgorithms.rootFidelity (ρ0 ⊗ₖ ρ0) (ρ1 ⊗ₖ ρ1) ∧
    QAlgorithms.rootFidelity (ρ0 ⊗ₖ ρ0) (ρ1 ⊗ₖ ρ1) = (QAlgorithms.rootFidelity ρ0 ρ1) ^ 2 ∧
    (QAlgorithms.rootFidelity ρ0 ρ1 = 1 ∨ QAlgorithms.rootFidelity ρ0 ρ1 = 0) ∧
    (ρ0 = ρ1 ∨ ρ0 * ρ1 = 0) := by sorry

end FuchsThesis.Broadcast
