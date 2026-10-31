-- Prove2me | Theorems.Thm_FuchsThesis_Fidelity_attaining_basis
-- name    : FuchsThesis.Fidelity.attaining_basis
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:55:32.366479+00:00
-- url     : https://prove2.me/theorems/580407ac-a240-4b29-9135-ab4ddbc78b48
-- title:
--   §3.3.1, (3.66)–(3.74) — an orthogonal measurement attains the overlap, for all states
-- statement:
--   Let $\hat\rho_0, \hat\rho_1$ be density operators on a $D$-dimensional space, invertible or not. There is an orthonormal basis $\{|b\rangle\}$ of the whole space such that
--
--   1. each $|b\rangle$ lies in the null subspace of $\hat\rho_1$ or in its support;
--   2. the projectors $\hat E_b = |b\rangle\langle b|$ form a POVM;
--   3. this measurement attains the fidelity formula:
--
--   $$
--   \sum_b \sqrt{\mathrm{tr}\,\hat\rho_0\hat E_b}\,\sqrt{\mathrm{tr}\,\hat\rho_1\hat E_b} \;=\; \mathrm{tr}\sqrt{\hat\rho_1^{1/2}\hat\rho_0\hat\rho_1^{1/2}} .
--   $$
--
--   Together with the lower bound (3.65) this gives Eq. (3.28) and shows that the minimum is reached by an orthogonal projection-valued measurement.
--
--   **Formalization Note** Outcomes are `Fin (Fintype.card n)`, the dimension $D$. Clause 2 follows from orthonormality and is stated so that the result plugs directly into the POVM optimization.
--
--   Differences from the source:
--   - generalization: for singular ρ̂₁: m one-dimensional projectors on the support of ρ̂₁ plus the single projector Π̂_null, (3.69)–(3.74) → a rank-one orthonormal basis, each vector in the support or the null subspace of ρ̂₁; reason: the basis vectors in the null subspace are an orthonormal basis of it, their projectors sum to Π̂_null, and each has p₁(b) = 0, so merging them gives the source measurement with the same value
--   - reading: the invertible-case measurement is the eigenbasis of M̂ and the singular-case one solves (3.74) → the existence of the measurement and its value; the eigenvalue equations are not in the conclusion; reason: they are the construction used in the proof; the claim the section establishes is attainment of (3.28)
--   - encoding: ∑_b √p₀(b) √p₁(b) → `FuchsVdGraaf.bhattacharyya`, ∑_b √(p₀(b) p₁(b)); reason: equal because p_k(b) ≥ 0 (proved in the mission sanity file); the published definition is reused
--   - encoding: tr of an operator that is nonnegative (or a real probability) → real part `.re` of the complex matrix trace; reason: the trace is real here; `.re` only moves the value from ℂ to ℝ
-- source:
--   Fuchs, Distinguishability and Accessible Information in Quantum Theory, arXiv:quant-ph/9601020v1, §3.3.1, eqs. (3.66)–(3.74), pp.53–54 (PDF pp.62–63)

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

/-- Fuchs, arXiv:quant-ph/9601020v1, §3.3.1, pp.53–54 (PDF pp.62–63), eqs. (3.66)–(3.74): for all
density operators, invertible or not, an orthogonal measurement attains the statistical overlap
`tr √(ρ̂₁^{1/2} ρ̂₀ ρ̂₁^{1/2})`. There is an orthonormal basis `{|b⟩}` of the whole space, each vector
lying in the support of `ρ̂₁` or in its null subspace, whose projectors `Ê_b = |b⟩⟨b|` form a POVM
with `∑_b √(tr ρ̂₀Ê_b) √(tr ρ̂₁Ê_b) = tr √(ρ̂₁^{1/2} ρ̂₀ ρ̂₁^{1/2})`.

**Formalization Note.** Outcomes are `Fin (Fintype.card n)`, the dimension of the space. The
source's measurement for singular `ρ̂₁` is `m` one-dimensional projectors on the support plus the
one projector `Π̂_null`, (3.69)–(3.74). The vectors here that lie in the null subspace are an
orthonormal basis of it, and their projectors sum to `Π̂_null`; each has `p₁(b) = 0`, so merging
them recovers the source's measurement with the same value. The left side is
`FuchsVdGraaf.bhattacharyya`, equal to `∑_b √p₀(b) √p₁(b)` because `p_k(b) ≥ 0`. -/
theorem attaining_basis {n : Type} [Fintype n] [DecidableEq n] (ρ0 ρ1 : Matrix n n ℂ)
    (h0 : IsDensityOperator ρ0) (h1 : IsDensityOperator ρ1) :
    ∃ e : Fin (Fintype.card n) → (n → ℂ),
      (∀ a b, star (e a) ⬝ᵥ e b = if a = b then 1 else 0) ∧
      (∀ b, ρ1 *ᵥ e b = 0 ∨ e b ∈ LinearMap.range ρ1.mulVecLin) ∧
      IsPOVM (fun b => vecMulVec (e b) (star (e b))) ∧
      bhattacharyya (outcomeDist ρ0 (fun b => vecMulVec (e b) (star (e b))))
          (outcomeDist ρ1 (fun b => vecMulVec (e b) (star (e b)))) =
        (Matrix.trace (CFC.sqrt (CFC.sqrt ρ1 * ρ0 * CFC.sqrt ρ1))).re := by sorry

end FuchsThesis.Fidelity
