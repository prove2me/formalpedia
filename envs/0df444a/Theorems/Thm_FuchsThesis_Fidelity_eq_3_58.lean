-- Prove2me | Theorems.Thm_FuchsThesis_Fidelity_eq_3_58
-- name    : FuchsThesis.Fidelity.eq_3_58
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:55:41.518737+00:00
-- url     : https://prove2.me/theorems/c97aa88c-3fcb-4a49-a7ef-efdda08cb075
-- title:
--   Eq. (3.58) — $\sum_b\sqrt{p_0(b)}\sqrt{p_1(b)} \ge |\mathrm{tr}(\hat U\hat\rho_0^{1/2}\hat\rho_1^{1/2})|$
-- statement:
--   Let $\hat\rho_0, \hat\rho_1$ be density operators on a finite-dimensional space. For every POVM $\{\hat E_b\}$ and every unitary operator $\hat U$,
--
--   $$
--   \sum_b \sqrt{p_0(b)}\,\sqrt{p_1(b)} \;\ge\; \Bigl|\mathrm{tr}\bigl(\hat U\hat\rho_0^{1/2}\hat\rho_1^{1/2}\bigr)\Bigr| ,
--   $$
--
--   where $p_k(b) = \mathrm{tr}(\hat\rho_k\hat E_b)$. The right side does not depend on the measurement, so it bounds the statistical overlap of every POVM at once.
--
--   **Formalization Note** The supposition on p.52 that the states are invertible belongs to the equality analysis; it is not a hypothesis of the inequality.
--
--   Differences from the source:
--   - encoding: ∑_b √p₀(b) √p₁(b) → `FuchsVdGraaf.bhattacharyya`, ∑_b √(p₀(b) p₁(b)); reason: equal because p_k(b) ≥ 0 (proved in the mission sanity file); the published definition is reused
--   - encoding: POVM {Ê_b} with arbitrarily many outcomes, (1.33)–(1.34) → `IsPOVM E` for `E : Fin m → Matrix n n ℂ`, any `m`; reason: covers every finite outcome count; the space is ℂ^n for any finite index type n
--   - encoding: tr of an operator that is nonnegative (or a real probability) → real part `.re` of the complex matrix trace; reason: the trace is real here; `.re` only moves the value from ℂ to ℝ
-- source:
--   Fuchs, Distinguishability and Accessible Information in Quantum Theory, arXiv:quant-ph/9601020v1, eq. (3.58), p.52 (PDF p.61)

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

/-- Fuchs, arXiv:quant-ph/9601020v1, eq. (3.58), p.52 (PDF p.61): summing (3.55) on `b`, for every
POVM `{Ê_b}` and every unitary `Û`,
`∑_b √p₀(b) √p₁(b) ≥ |tr(Û ρ̂₀^{1/2} ρ̂₁^{1/2})|`.

**Formalization Note.** The source's supposition that `ρ̂₀, ρ̂₁` are invertible (p.52) belongs to
the equality analysis, so it is not a hypothesis here. The left side is
`FuchsVdGraaf.bhattacharyya (outcomeDist ρ0 E) (outcomeDist ρ1 E) = ∑ b, √(p₀(b) p₁(b))`, which
equals `∑_b √p₀(b) √p₁(b)` because `p_k(b) ≥ 0`. -/
theorem eq_3_58 {n : Type} [Fintype n] [DecidableEq n] (ρ0 ρ1 : Matrix n n ℂ)
    (h0 : IsDensityOperator ρ0) (h1 : IsDensityOperator ρ1)
    {m : ℕ} (E : Fin m → Matrix n n ℂ) (hE : IsPOVM E)
    (U : Matrix n n ℂ) (hU : U ∈ unitaryGroup n ℂ) :
    bhattacharyya (outcomeDist ρ0 E) (outcomeDist ρ1 E) ≥
      ‖Matrix.trace (U * CFC.sqrt ρ0 * CFC.sqrt ρ1)‖ := by sorry

end FuchsThesis.Fidelity
