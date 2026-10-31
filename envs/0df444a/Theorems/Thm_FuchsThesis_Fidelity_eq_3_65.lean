-- Prove2me | Theorems.Thm_FuchsThesis_Fidelity_eq_3_65
-- name    : FuchsThesis.Fidelity.eq_3_65
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:55:53.294278+00:00
-- url     : https://prove2.me/theorems/0e5acb54-0e4f-4514-8c11-17b71cbe3d26
-- title:
--   Eqs. (3.63), (3.65) — every POVM has overlap at least $\mathrm{tr}\sqrt{\hat\rho_1^{1/2}\hat\rho_0\hat\rho_1^{1/2}}$
-- statement:
--   Let $\hat\rho_0, \hat\rho_1$ be density operators on a finite-dimensional space. There is a unitary operator $\hat U_c$ with
--
--   $$
--   \hat U_c\hat\rho_0^{1/2}\hat\rho_1^{1/2} = \sqrt{\hat\rho_1^{1/2}\hat\rho_0\hat\rho_1^{1/2}} ,
--   $$
--
--   and for every POVM $\{\hat E_b\}$, with $p_k(b) = \mathrm{tr}(\hat\rho_k\hat E_b)$,
--
--   $$
--   \sum_b \sqrt{p_0(b)}\,\sqrt{p_1(b)} \;\ge\; \Bigl|\mathrm{tr}\bigl(\hat U_c\hat\rho_0^{1/2}\hat\rho_1^{1/2}\bigr)\Bigr| \;=\; \mathrm{tr}\sqrt{\hat\rho_1^{1/2}\hat\rho_0\hat\rho_1^{1/2}} .
--   $$
--
--   This is the lower-bound half of Eq. (3.28): no measurement has a smaller statistical overlap than the quantum fidelity formula.
--
--   **Formalization Note** No invertibility is assumed. $\hat U_c$ does not depend on the POVM.
--
--   Differences from the source:
--   - encoding: ∑_b √p₀(b) √p₁(b) → `FuchsVdGraaf.bhattacharyya`, ∑_b √(p₀(b) p₁(b)); reason: equal because p_k(b) ≥ 0 (proved in the mission sanity file); the published definition is reused
--   - encoding: POVM {Ê_b} with arbitrarily many outcomes, (1.33)–(1.34) → `IsPOVM E` for `E : Fin m → Matrix n n ℂ`, any `m`; reason: covers every finite outcome count; the space is ℂ^n for any finite index type n
--   - encoding: tr of an operator that is nonnegative (or a real probability) → real part `.re` of the complex matrix trace; reason: the trace is real here; `.re` only moves the value from ℂ to ℝ
--   - reading: the middle member √((ρ̂₀^{1/2}ρ̂₁^{1/2})†(ρ̂₀^{1/2}ρ̂₁^{1/2})) of (3.63) → omitted; (3.63) stated as Û_c ρ̂₀^{1/2}ρ̂₁^{1/2} = √(ρ̂₁^{1/2}ρ̂₀ρ̂₁^{1/2}); reason: the middle member is the same matrix written as A†A with A = ρ̂₀^{1/2}ρ̂₁^{1/2}, an identity of the definitions
-- source:
--   Fuchs, Distinguishability and Accessible Information in Quantum Theory, arXiv:quant-ph/9601020v1, eqs. (3.63) and (3.65), p.53 (PDF p.62)

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

/-- Fuchs, arXiv:quant-ph/9601020v1, eqs. (3.63) and (3.65), p.53 (PDF p.62): there is a unitary
`Û_c` with `Û_c ρ̂₀^{1/2} ρ̂₁^{1/2} = √(ρ̂₁^{1/2} ρ̂₀ ρ̂₁^{1/2})`, and for it, for every POVM,
`∑_b √p₀(b) √p₁(b) ≥ |tr(Û_c ρ̂₀^{1/2} ρ̂₁^{1/2})| = tr √(ρ̂₁^{1/2} ρ̂₀ ρ̂₁^{1/2})`.

**Formalization Note.** No invertibility is assumed. (3.63) uses `(ρ̂₀^{1/2} ρ̂₁^{1/2})†(ρ̂₀^{1/2}
ρ̂₁^{1/2}) = ρ̂₁^{1/2} ρ̂₀ ρ̂₁^{1/2}`. `Û_c` is chosen once, before the POVM, as in the source. The
left side is `FuchsVdGraaf.bhattacharyya`, equal to `∑_b √p₀(b) √p₁(b)` because `p_k(b) ≥ 0`. -/
theorem eq_3_65 {n : Type} [Fintype n] [DecidableEq n] (ρ0 ρ1 : Matrix n n ℂ)
    (h0 : IsDensityOperator ρ0) (h1 : IsDensityOperator ρ1) :
    ∃ Uc ∈ unitaryGroup n ℂ,
      Uc * CFC.sqrt ρ0 * CFC.sqrt ρ1 = CFC.sqrt (CFC.sqrt ρ1 * ρ0 * CFC.sqrt ρ1) ∧
      ‖Matrix.trace (Uc * CFC.sqrt ρ0 * CFC.sqrt ρ1)‖ =
        (Matrix.trace (CFC.sqrt (CFC.sqrt ρ1 * ρ0 * CFC.sqrt ρ1))).re ∧
      ∀ (m : ℕ) (E : Fin m → Matrix n n ℂ), IsPOVM E →
        bhattacharyya (outcomeDist ρ0 E) (outcomeDist ρ1 E) ≥
          ‖Matrix.trace (Uc * CFC.sqrt ρ0 * CFC.sqrt ρ1)‖ := by sorry

end FuchsThesis.Fidelity
