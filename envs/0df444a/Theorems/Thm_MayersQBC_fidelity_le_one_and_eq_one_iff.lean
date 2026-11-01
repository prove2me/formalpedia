-- Prove2me | Theorems.Thm_MayersQBC_fidelity_le_one_and_eq_one_iff
-- name    : MayersQBC.fidelity_le_one_and_eq_one_iff
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:27:45.856845+00:00
-- url     : https://prove2.me/theorems/06f16a49-1cbd-4440-806a-603e9ce1b0af
-- title:
--   Section c, p.2 — the fidelity is at most 1, and equals 1 iff the density matrices are identical
-- statement:
--   Let $\rho$ and $\sigma$ be density matrices (positive semidefinite, trace one) on a finite-dimensional system, and let
--
--   $$
--   F(\rho,\sigma) = \Big(\operatorname{Tr}\sqrt{\sqrt\rho\,\sigma\sqrt\rho}\Big)^2
--   $$
--
--   be their fidelity (Jozsa). Then
--
--   $$
--   F(\rho,\sigma) \le 1, \qquad\text{and}\qquad F(\rho,\sigma) = 1 \iff \rho = \sigma .
--   $$
--
--   The paper uses this to identify perfect concealment (expected fidelity $1$) with identical Bob states for almost every transcript, and to read the Uhlmann bound (4) in Jozsa's convention.
--
--   **Formalization Note** $F$ is the square of the published `rootFidelity`.
--
--   Differences from the source:
--   - encoding: the fidelity [9] (Jozsa) F(ρ, σ) = (Tr √(√ρ σ √ρ))² → QAlgorithms.rootFidelity ρ σ ^ 2; reason: rootFidelity is Tr √(√ρ σ √ρ); its square is Jozsa's fidelity, the one the paper cites
-- source:
--   Mayers, Unconditionally secure quantum bit commitment is impossible, arXiv:quant-ph/9605044v2, section c, p.2 ("The fidelity is never greater than 1 and is equal to 1 if and only if the two density matrices are identical.")

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Defs_QuantumInformation
open QAlgorithms

namespace MayersQBC

/-- Mayers, arXiv:quant-ph/9605044v2, section c, p.2: "The fidelity is never greater than 1 and
is equal to 1 if and only if the two density matrices are identical." For density matrices
`ρ, σ` on a finite system, Jozsa's fidelity `F(ρ, σ) = (Tr √(√ρ σ √ρ))²` satisfies `F(ρ, σ) ≤ 1`,
and `F(ρ, σ) = 1` if and only if `ρ = σ`.

**Formalization Note.** The paper's fidelity [9] (Jozsa) is the square of the published
`QAlgorithms.rootFidelity`; a density matrix is positive semidefinite with trace `1`
(`QAlgorithms.IsDensityMatrix`). -/
theorem fidelity_le_one_and_eq_one_iff {ι : Type} [Fintype ι] [DecidableEq ι]
    (ρ σ : Matrix ι ι ℂ) (hρ : IsDensityMatrix ρ) (hσ : IsDensityMatrix σ) :
    rootFidelity ρ σ ^ 2 ≤ 1 ∧ (rootFidelity ρ σ ^ 2 = 1 ↔ ρ = σ) := by sorry

end MayersQBC
