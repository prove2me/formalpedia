-- Prove2me | Theorems.Thm_FuchsThesis_Fidelity_eq_3_28
-- name    : FuchsThesis.Fidelity.eq_3_28
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:56:06.191266+00:00
-- url     : https://prove2.me/theorems/23b4570d-ba4a-4c83-a2ce-94e86e3c4561
-- title:
--   Eq. (3.28) — $F(\hat\rho_0,\hat\rho_1) = \mathrm{tr}\sqrt{\hat\rho_1^{1/2}\hat\rho_0\hat\rho_1^{1/2}}$, the quantum fidelity formula
-- statement:
--   Let $\hat\rho_0, \hat\rho_1$ be density operators on a finite-dimensional space. The **quantum fidelity** is the optimal statistical overlap over all measurements,
--
--   $$
--   F(\hat\rho_0,\hat\rho_1) = \min_{\{\hat E_b\}} \sum_b \sqrt{\mathrm{tr}\,\hat\rho_0\hat E_b}\,\sqrt{\mathrm{tr}\,\hat\rho_1\hat E_b} ,
--   $$
--
--   the minimum taken over all POVMs $\{\hat E_b\}$. Then the minimum is attained and
--
--   $$
--   F(\hat\rho_0,\hat\rho_1) = \mathrm{tr}\sqrt{\hat\rho_1^{1/2}\hat\rho_0\hat\rho_1^{1/2}} ,
--   $$
--
--   where $\hat A^{1/2}$ is the unique nonnegative square root of a nonnegative operator $\hat A$. The states need not be invertible.
--
--   This gives the operational meaning of Uhlmann's transition probability and the Bures distance: their common quantity is exactly the classical overlap of the best measurement.
--
--   **Formalization Note** The left side is defined as an infimum over POVMs, never by the closed formula. The published definition `FuchsVdGraaf.qBhattacharyya` is this same quantity under the name used by Fuchs and van de Graaf.
--
--   Differences from the source:
--   - encoding: min over POVMs in (3.27) → `qBhattacharyya` (`sInf` of the values) together with a conjunct giving a POVM that attains the value; reason: the two conjuncts together say exactly that the minimum exists and equals the right side
--   - encoding: ∑_b √p₀(b) √p₁(b) → `FuchsVdGraaf.bhattacharyya`, ∑_b √(p₀(b) p₁(b)); reason: equal because p_k(b) ≥ 0 (proved in the mission sanity file); the published definition is reused
--   - encoding: POVM {Ê_b} with arbitrarily many outcomes, (1.33)–(1.34) → `IsPOVM E` for `E : Fin m → Matrix n n ℂ`, any `m`; reason: covers every finite outcome count; the space is ℂ^n for any finite index type n
--   - encoding: tr of an operator that is nonnegative (or a real probability) → real part `.re` of the complex matrix trace; reason: the trace is real here; `.re` only moves the value from ℂ to ℝ
-- source:
--   Fuchs, Distinguishability and Accessible Information in Quantum Theory, arXiv:quant-ph/9601020v1, eq. (3.28), p.49 (PDF p.58), with the definition (3.27), p.47 (PDF p.56)

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_FuchsVdGraaf_IsPOVM
import Definitions.Def_FuchsVdGraaf_outcomeDist
import Definitions.Def_FuchsVdGraaf_bhattacharyya
import Definitions.Def_FuchsVdGraaf_qBhattacharyya
open Matrix
open scoped MatrixOrder ComplexOrder
open WildeQIT FuchsVdGraaf

namespace FuchsThesis.Fidelity

/-- Fuchs, *Distinguishability and Accessible Information in Quantum Theory*,
arXiv:quant-ph/9601020v1, eq. (3.28) with the definition (3.27), p.49 (PDF p.58) and p.47 (PDF
p.56): for all density operators `ρ̂₀`, `ρ̂₁` on a finite-dimensional space, the quantum fidelity
`F(ρ̂₀, ρ̂₁) = min_{Ê_b} ∑_b √(tr ρ̂₀Ê_b) √(tr ρ̂₁Ê_b)` equals `tr √(ρ̂₁^{1/2} ρ̂₀ ρ̂₁^{1/2})`.

**Formalization Note.** The left side is the optimum over all POVMs with any finite number of
outcomes, `FuchsVdGraaf.qBhattacharyya`, an `sInf` of values (Fuchs and van de Graaf's name for the
same quantity); the closed formula is not part of its definition. Its summand `√(p₀(b) p₁(b))`
equals `√p₀(b) √p₁(b)` because `p_k(b) ≥ 0`. The source's "min" is the `sInf` together with the
second conjunct, that some POVM attains the value. `A^{1/2}` is `CFC.sqrt`, the unique nonnegative
square root on positive semidefinite matrices; the trace on the right is real and `.re` extracts
it. Invertibility is not assumed. -/
theorem eq_3_28 {n : Type} [Fintype n] [DecidableEq n] (ρ0 ρ1 : Matrix n n ℂ)
    (h0 : IsDensityOperator ρ0) (h1 : IsDensityOperator ρ1) :
    qBhattacharyya ρ0 ρ1 = (Matrix.trace (CFC.sqrt (CFC.sqrt ρ1 * ρ0 * CFC.sqrt ρ1))).re ∧
    ∃ (m : ℕ) (E : Fin m → Matrix n n ℂ), IsPOVM E ∧
      bhattacharyya (outcomeDist ρ0 E) (outcomeDist ρ1 E) =
        (Matrix.trace (CFC.sqrt (CFC.sqrt ρ1 * ρ0 * CFC.sqrt ρ1))).re := by sorry

end FuchsThesis.Fidelity
