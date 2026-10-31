-- Prove2me | Theorems.Thm_FuchsThesis_Helstrom_eq_3_15
-- name    : FuchsThesis.Helstrom.eq_3_15
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:56:24.200363+00:00
-- url     : https://prove2.me/theorems/53326b7c-e1ee-43f5-8f09-d5cf126d91e5
-- title:
--   Eq. (3.15) — the error of a binary POVM is $\pi_0 + \mathrm{tr}(\hat\Gamma\hat E_0)$
-- statement:
--   Let $\hat\rho_0, \hat\rho_1$ be density operators, $\pi_0, \pi_1 \ge 0$ with $\pi_0 + \pi_1 = 1$, and let $\{\hat E_0, \hat E_1\}$ be an arbitrary binary-valued POVM, so that $\hat E_0 + \hat E_1 = \hat{\mathbb 1}$. Then its error probability (3.10) is
--
--   $$
--   P_e = \pi_0\,\mathrm{tr}\big(\hat\rho_0(\hat{\mathbb 1} - \hat E_0)\big) + \pi_1\,\mathrm{tr}(\hat\rho_1\hat E_0) = \pi_0 + \mathrm{tr}\big((\pi_1\hat\rho_1 - \pi_0\hat\rho_0)\hat E_0\big).
--   $$
--
--   Minimizing the error probability therefore reduces to minimizing $\mathrm{tr}(\hat\Gamma\hat E_0)$, with $\hat\Gamma = \pi_1\hat\rho_1 - \pi_0\hat\rho_0$, over all operators $0 \le \hat E_0 \le \hat{\mathbb 1}$.
--
--   Differences from the source:
--   - encoding: binary POVM $\{\hat E_0,\hat E_1\}$ and $\mathrm{tr}$ → `E : Fin 2 → Matrix n n ℂ` with `FuchsVdGraaf.IsPOVM E` and the real part of the matrix trace; reason: Lean convention, the traces involved are real.
--   - encoding: the three-line chain (3.15) → the equality of its two ends, (3.10) $=\pi_0 + \mathrm{tr}(\hat\Gamma\hat E_0)$; reason: the middle lines are the steps of the computation.
-- source:
--   Fuchs, Distinguishability and Accessible Information in Quantum Theory, arXiv:quant-ph/9601020v1, eq. (3.15) with (3.14), p.45 (PDF p.54)

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_FuchsVdGraaf_IsPOVM
import Definitions.Def_FuchsThesis_Helstrom_binaryError
import Definitions.Def_FuchsThesis_Helstrom_gammaOp

open scoped ComplexOrder

namespace FuchsThesis.Helstrom

/-- Fuchs, *Distinguishability and Accessible Information in Quantum Theory*,
arXiv:quant-ph/9601020v1, eq. (3.15), p.45 (PDF p.54): for an arbitrary binary-valued POVM
`{Ê₀, Ê₁}` (so `Ê₀ + Ê₁ = 1̂`, (3.14)), the error probability (3.10) is
`P_e = π₀tr(ρ̂₀(1̂ − Ê₀)) + π₁tr(ρ̂₁Ê₀) = π₀ + tr((π₁ρ̂₁ − π₀ρ̂₀)Ê₀)`.

**Formalization Note.** The binary POVM is `E : Fin 2 → Matrix n n ℂ` with `Ê₀ = E 0`; `P_e` is
`binaryError` (3.10); `π₁ρ̂₁ − π₀ρ̂₀` is `gammaOp` (3.12); traces are real parts. -/
theorem eq_3_15 {n : Type} [Fintype n] [DecidableEq n] (π0 π1 : ℝ) (hπ0 : 0 ≤ π0)
    (hπ1 : 0 ≤ π1) (hπ : π0 + π1 = 1) (ρ0 ρ1 : Matrix n n ℂ)
    (h0 : WildeQIT.IsDensityOperator ρ0) (h1 : WildeQIT.IsDensityOperator ρ1)
    (E : Fin 2 → Matrix n n ℂ) (hE : FuchsVdGraaf.IsPOVM E) :
    binaryError π0 π1 ρ0 ρ1 E = π0 + (Matrix.trace (gammaOp π0 π1 ρ0 ρ1 * E 0)).re := by sorry

end FuchsThesis.Helstrom
