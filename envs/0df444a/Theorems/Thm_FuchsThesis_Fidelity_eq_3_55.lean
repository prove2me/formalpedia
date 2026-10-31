-- Prove2me | Theorems.Thm_FuchsThesis_Fidelity_eq_3_55
-- name    : FuchsThesis.Fidelity.eq_3_55
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:55:52.658166+00:00
-- url     : https://prove2.me/theorems/562b14aa-0b6a-43ae-a38d-1a10f6be1dd5
-- title:
--   Eq. (3.55) — $\sqrt{p_0(b)}\sqrt{p_1(b)} \ge |\mathrm{tr}(\hat U\hat\rho_0^{1/2}\hat E_b\hat\rho_1^{1/2})|$
-- statement:
--   Let $\hat\rho_0, \hat\rho_1$ be density operators on a finite-dimensional space, $\{\hat E_b\}$ a POVM, and $p_k(b) = \mathrm{tr}(\hat\rho_k\hat E_b)$. For every outcome $b$ and every unitary operator $\hat U$,
--
--   $$
--   \sqrt{p_0(b)}\,\sqrt{p_1(b)} \;\ge\; \Bigl|\mathrm{tr}\bigl(\hat U\hat\rho_0^{1/2}\hat E_b\hat\rho_1^{1/2}\bigr)\Bigr| .
--   $$
--
--   The freedom in $\hat U$ is what later allows equality to be attained by a measurement, which the case $\hat U = \hat{\mathbb 1}$ does not.
--
--   **Formalization Note** Neither state need be invertible. The equality condition (3.56) is not part of the statement.
--
--   Differences from the source:
--   - encoding: POVM {Ê_b} with arbitrarily many outcomes, (1.33)–(1.34) → `IsPOVM E` for `E : Fin m → Matrix n n ℂ`, any `m`; reason: covers every finite outcome count; the space is ℂ^n for any finite index type n
--   - encoding: tr of an operator that is nonnegative (or a real probability) → real part `.re` of the complex matrix trace; reason: the trace is real here; `.re` only moves the value from ℂ to ℝ
--   - reading: the four-member chain (3.55), with the intermediate Schwarz-inequality members √tr(X†X)√tr(Y†Y) and |tr(X†Y)| → the inequality between its first and last members; reason: the intermediate members are the steps of the proof (the cyclic trace rewriting and the Schwarz inequality (3.37)); the claim the display establishes is the end-to-end bound
-- source:
--   Fuchs, Distinguishability and Accessible Information in Quantum Theory, arXiv:quant-ph/9601020v1, eq. (3.55), p.52 (PDF p.61)

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

/-- Fuchs, arXiv:quant-ph/9601020v1, eq. (3.55), p.52 (PDF p.61): for every POVM `{Ê_b}`, every
outcome `b` and every unitary `Û`,
`√p₀(b) √p₁(b) ≥ |tr(Û ρ̂₀^{1/2} Ê_b ρ̂₁^{1/2})|`, where `p_k(b) = tr(ρ̂_k Ê_b)` (eq. (3.38)).

**Formalization Note.** Neither state need be invertible. The Hilbert space is `ℂ^n` for an
arbitrary finite index type `n`; a POVM has outcomes `Fin m` for an arbitrary `m`
(`FuchsVdGraaf.IsPOVM`), and `p_k(b)` is `FuchsVdGraaf.outcomeDist ρ_k E b`, the real part of a
trace that is real and nonnegative here. `|·|` is the complex modulus. The equality condition
(3.56) is a remark for the proof and is not stated. -/
theorem eq_3_55 {n : Type} [Fintype n] [DecidableEq n] (ρ0 ρ1 : Matrix n n ℂ)
    (h0 : IsDensityOperator ρ0) (h1 : IsDensityOperator ρ1)
    {m : ℕ} (E : Fin m → Matrix n n ℂ) (hE : IsPOVM E) (b : Fin m)
    (U : Matrix n n ℂ) (hU : U ∈ unitaryGroup n ℂ) :
    Real.sqrt (outcomeDist ρ0 E b) * Real.sqrt (outcomeDist ρ1 E b) ≥
      ‖Matrix.trace (U * CFC.sqrt ρ0 * E b * CFC.sqrt ρ1)‖ := by sorry

end FuchsThesis.Fidelity
