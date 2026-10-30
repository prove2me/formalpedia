-- Prove2me | Theorems.Thm_FuchsVdGraaf_proposition_3
-- name    : FuchsVdGraaf.proposition_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T03:16:01.83638+00:00
-- url     : https://prove2.me/theorems/eaaac3e6-596f-4f00-8195-1133018237aa
-- title:
--   Proposition 3 — $K(\rho_0,\rho_1) = \tfrac12\sum_j|\lambda_j| = \tfrac12\mathrm{Tr}|\rho_0-\rho_1|$
-- statement:
--   Let $\rho_0, \rho_1$ be two $N\times N$ density matrices and let $\lambda_1,\dots,\lambda_N$ be the eigenvalues (with multiplicity) of $\rho_0 - \rho_1$. Then the quantum Kolmogorov distance, maximised over all POVMs, is
--
--   $$
--   K(\rho_0,\rho_1) = \frac12\sum_{j=1}^{N}|\lambda_j| = \frac12\,\mathrm{Tr}|\rho_0 - \rho_1| .
--   $$
--
--   Both equalities are asserted. The quantum Kolmogorov distance is therefore the trace distance, which in particular satisfies the triangle inequality.
--
--   Differences from the source:
--   - reading: $\max_{E\in\mathcal M}$ → supremum over the set of values at all POVMs; reason: the paper's own "more carefully" remark (p.10).
--   - encoding: POVMs $\langle E_1,\dots,E_m\rangle$ and $\mathrm{Tr}(\rho E_x)$ → `E : Fin m → Matrix n n ℂ` for every `m : ℕ` and the real part of the trace; reason: Lean convention, covers every finite POVM.
--   - encoding: $\mathrm{Tr}|\rho_0-\rho_1|$ and the eigenvalues $\lambda_j$ → `WildeQIT.traceNorm (ρ0 - ρ1)` and `IsHermitian.eigenvalues`; reason: for Hermitian $\Gamma$, $\sqrt{\Gamma^\dagger\Gamma} = |\Gamma|$; same values.
-- source:
--   Fuchs and van de Graaf, Cryptographic Distinguishability Measures for Quantum Mechanical States, arXiv:quant-ph/9712042v2, Proposition 3, eq. (21), p.12

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_WildeQIT_traceNorm
import Definitions.Def_FuchsVdGraaf_qKolmogorov

open scoped ComplexOrder

namespace FuchsVdGraaf

/-- Fuchs and van de Graaf, arXiv:quant-ph/9712042v2, Proposition 3, eq. (21), p.12: the
Kolmogorov distance between two density matrices `ρ₀`, `ρ₁` equals
`K(ρ₀, ρ₁) = ½ ∑_{j=1}^{N} |λ_j| = ½ Tr|ρ₀ − ρ₁|`, where the `λ_j` are the eigenvalues of
`ρ₀ − ρ₁`.

**Formalization Note.** `K(ρ₀, ρ₁)` is `qKolmogorov`, the supremum over all POVMs with any finite
number of outcomes. The eigenvalues are those of the Hermitian matrix `ρ₀ − ρ₁`
(`Matrix.IsHermitian.eigenvalues`, with multiplicity). `Tr|ρ₀ − ρ₁|` is `WildeQIT.traceNorm`. -/
theorem proposition_3 {n : Type} [Fintype n] [DecidableEq n] (ρ0 ρ1 : Matrix n n ℂ)
    (h0 : WildeQIT.IsDensityOperator ρ0) (h1 : WildeQIT.IsDensityOperator ρ1) :
    qKolmogorov ρ0 ρ1 =
        1 / 2 * ∑ j, |(h0.1.isHermitian.sub h1.1.isHermitian).eigenvalues j| ∧
      qKolmogorov ρ0 ρ1 = 1 / 2 * WildeQIT.traceNorm (ρ0 - ρ1) := by sorry

end FuchsVdGraaf
