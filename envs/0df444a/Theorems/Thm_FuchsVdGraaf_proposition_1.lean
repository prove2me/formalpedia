-- Prove2me | Theorems.Thm_FuchsVdGraaf_proposition_1
-- name    : FuchsVdGraaf.proposition_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T03:16:03.223036+00:00
-- url     : https://prove2.me/theorems/db08f6ad-c66f-42fa-b6fb-57d583f8318f
-- title:
--   Proposition 1 (Helstrom) — $\mathrm{PE}(\rho_0,\rho_1) = \tfrac12 - \tfrac14\sum_j|\lambda_j| = \tfrac12 - \tfrac14\mathrm{Tr}|\rho_0-\rho_1|$
-- statement:
--   Let $\rho_0, \rho_1$ be two arbitrary $N\times N$ density matrices and let $\lambda_1,\dots,\lambda_N$ be the eigenvalues (with multiplicity) of the Hermitian matrix $\rho_0 - \rho_1$. Then the quantum probability of error, minimised over all POVMs, is
--
--   $$
--   \mathrm{PE}(\rho_0,\rho_1) = \frac12 - \frac14\sum_{j=1}^{N}|\lambda_j| = \frac12 - \frac14\,\mathrm{Tr}|\rho_0 - \rho_1| .
--   $$
--
--   Both equalities are asserted. This is Helstrom's formula: the optimal error of discriminating two equiprobable states is a function of their trace distance.
--
--   Differences from the source:
--   - reading: $\min_{E\in\mathcal M}$ → infimum over the set of values at all POVMs; reason: the paper's own "more carefully, one should use infimum" (p.10).
--   - encoding: POVMs $\langle E_1,\dots,E_m\rangle$ and $\mathrm{Tr}(\rho E_x)$ → `E : Fin m → Matrix n n ℂ` for every `m : ℕ` and the real part of the trace; reason: Lean convention, covers every finite POVM.
--   - encoding: $\mathrm{Tr}|\rho_0-\rho_1|$ and the eigenvalues $\lambda_j$ → `WildeQIT.traceNorm (ρ0 - ρ1)` $= \mathrm{Re}\,\mathrm{Tr}\sqrt{\Gamma^\dagger\Gamma}$ and `IsHermitian.eigenvalues`; reason: for Hermitian $\Gamma$, $\sqrt{\Gamma^\dagger\Gamma} = |\Gamma|$; same values.
-- source:
--   Fuchs and van de Graaf, Cryptographic Distinguishability Measures for Quantum Mechanical States, arXiv:quant-ph/9712042v2, Proposition 1, eq. (17), p.11

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_WildeQIT_traceNorm
import Definitions.Def_FuchsVdGraaf_qErrorProb

open scoped ComplexOrder

namespace FuchsVdGraaf

/-- Fuchs and van de Graaf, arXiv:quant-ph/9712042v2, Proposition 1, eq. (17), p.11: for two
arbitrary density matrices `ρ₀`, `ρ₁`, the (quantum) probability of error equals
`PE(ρ₀, ρ₁) = ½ − ¼ ∑_{j=1}^{N} |λ_j| = ½ − ¼ Tr|ρ₀ − ρ₁|`, where the `λ_j` are the eigenvalues
of `ρ₀ − ρ₁`.

**Formalization Note.** `PE(ρ₀, ρ₁)` is `qErrorProb`, the infimum over all POVMs with any finite
number of outcomes. The eigenvalues are those of the Hermitian matrix `ρ₀ − ρ₁`
(`Matrix.IsHermitian.eigenvalues`, listed with multiplicity), the Hermitian proof being derived
from the two density-matrix hypotheses. `Tr|ρ₀ − ρ₁|` is the published `WildeQIT.traceNorm`. -/
theorem proposition_1 {n : Type} [Fintype n] [DecidableEq n] (ρ0 ρ1 : Matrix n n ℂ)
    (h0 : WildeQIT.IsDensityOperator ρ0) (h1 : WildeQIT.IsDensityOperator ρ1) :
    qErrorProb ρ0 ρ1 =
        1 / 2 - 1 / 4 * ∑ j, |(h0.1.isHermitian.sub h1.1.isHermitian).eigenvalues j| ∧
      qErrorProb ρ0 ρ1 = 1 / 2 - 1 / 4 * WildeQIT.traceNorm (ρ0 - ρ1) := by sorry

end FuchsVdGraaf
