-- Prove2me | Theorems.Thm_FuchsThesis_Helstrom_eq_3_11
-- name    : FuchsThesis.Helstrom.eq_3_11
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:56:39.346999+00:00
-- url     : https://prove2.me/theorems/b2350cdc-2652-4b57-8d56-8db69a8066d6
-- title:
--   Eq. (3.11) — the minimum over all POVMs equals the minimum over binary-valued POVMs
-- statement:
--   Let $\hat\rho_0, \hat\rho_1$ be density operators on a finite-dimensional Hilbert space and $\pi_0, \pi_1 \ge 0$ with $\pi_0 + \pi_1 = 1$. Then
--
--   $$
--   \min_{\{\hat E_b\}} \sum_b \min\big\{\pi_0\,\mathrm{tr}(\hat\rho_0\hat E_b),\ \pi_1\,\mathrm{tr}(\hat\rho_1\hat E_b)\big\}
--   = \min_{\{\hat E_0,\hat E_1\}} \Big(\pi_0\,\mathrm{tr}(\hat\rho_0\hat E_1) + \pi_1\,\mathrm{tr}(\hat\rho_1\hat E_0)\Big),
--   $$
--
--   where the left minimum runs over all POVMs with any finite number of outcomes and the right one over binary-valued POVMs. Both minima exist and are equal.
--
--   The statement says that any "measurement + guess" can be summarized by a single binary-valued POVM, so the quantum error probability (3.9) may be computed by optimizing the binary error (3.10) alone.
--
--   Differences from the source:
--   - encoding: $\min_{\{\hat E_b\}} = \min_{\{\hat E_0,\hat E_1\}}$ → one value $v$ that is the least element (`IsLeast`) of the set of values over every POVM `E : Fin m → Matrix n n ℂ` (any $m$) and of the set of values over every `E : Fin 2 → Matrix n n ℂ`; reason: "min A = min B" says both minima exist and coincide.
--   - encoding: $\mathrm{tr}(\hat\rho\hat E)$ → the real part of the matrix trace; reason: the trace is real for density operators and positive semidefinite $\hat E$.
-- source:
--   Fuchs, Distinguishability and Accessible Information in Quantum Theory, arXiv:quant-ph/9601020v1, eq. (3.11), p.44 (PDF p.53)

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_FuchsVdGraaf_IsPOVM
import Definitions.Def_FuchsThesis_Helstrom_bayesError
import Definitions.Def_FuchsThesis_Helstrom_binaryError

open scoped ComplexOrder

namespace FuchsThesis.Helstrom

/-- Fuchs, *Distinguishability and Accessible Information in Quantum Theory*,
arXiv:quant-ph/9601020v1, eq. (3.11), p.44 (PDF p.53): for density operators `ρ̂₀, ρ̂₁` and priors
`π₀, π₁`,
`min_{Ê_b} ∑_b min{π₀tr(ρ̂₀Ê_b), π₁tr(ρ̂₁Ê_b)} = min_{Ê₀,Ê₁} (π₀ tr(ρ̂₀Ê₁) + π₁ tr(ρ̂₁Ê₀))`,
the left minimum over all POVMs and the right one over binary-valued POVMs `{Ê₀, Ê₁}`.

**Formalization Note.** "`min A = min B`" is stated as: there is a value `v` that is the least
element (`IsLeast`) both of the set of values `bayesError π₀ π₁ ρ₀ ρ₁ E` over every POVM
`E : Fin m → Matrix n n ℂ` with any `m`, and of the set of values `binaryError π₀ π₁ ρ₀ ρ₁ E` over
every two-outcome POVM `E : Fin 2 → Matrix n n ℂ`. So both minima exist and coincide. -/
theorem eq_3_11 {n : Type} [Fintype n] [DecidableEq n] (π0 π1 : ℝ) (hπ0 : 0 ≤ π0)
    (hπ1 : 0 ≤ π1) (hπ : π0 + π1 = 1) (ρ0 ρ1 : Matrix n n ℂ)
    (h0 : WildeQIT.IsDensityOperator ρ0) (h1 : WildeQIT.IsDensityOperator ρ1) :
    ∃ v : ℝ,
      IsLeast {w : ℝ | ∃ (m : ℕ) (E : Fin m → Matrix n n ℂ),
        FuchsVdGraaf.IsPOVM E ∧ w = bayesError π0 π1 ρ0 ρ1 E} v ∧
      IsLeast {w : ℝ | ∃ E : Fin 2 → Matrix n n ℂ,
        FuchsVdGraaf.IsPOVM E ∧ w = binaryError π0 π1 ρ0 ρ1 E} v := by sorry

end FuchsThesis.Helstrom
