-- Prove2me | Theorems.Thm_OnlineShadow_LogRate_eq_8
-- name    : OnlineShadow.LogRate.eq_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T04:04:58.262513+00:00
-- url     : https://prove2.me/theorems/c31b09c8-fc21-446c-9d02-1b3441177ffb
-- title:
--   Eq. (8) — $\Phi_F^\dagger(X)=\frac12(U^\dagger XU+UXU^\dagger)$ with $U=\sqrt{1-F}+i\sqrt F$
-- statement:
--   Let $F$ be an operator with $0\preceq F\preceq1$ on a finite-dimensional space, and $\Phi_F^\dagger(X)=\sqrt F X\sqrt F+\sqrt{1-F}X\sqrt{1-F}$ the (adjoint) post-measurement channel of the two-outcome measurement $(\sqrt F,\sqrt{1-F})$.
--
--   **Eq. (8).** The matrix $U=\sqrt{1-F}+i\sqrt F$ is unitary, and for every operator $X$,
--   $$\Phi_F^\dagger(X)=\frac12\big(U^\dagger XU+UXU^\dagger\big).$$
--
--   This rewrites the measurement channel as an average of two unitary conjugations, which is what Lemma 4.8 controls.
--
--   **Formalization Note** Square roots are the positive square roots, by the functional calculus.
--
--   Differences from the source:
--   - generalization: F = f(A̅) the flag operator of a soft binary measurement → any operator 0 ⪯ F ⪯ 1 on a finite-dimensional space; reason: the derivation on p. 14 uses only 0 ⪯ F ⪯ 1; the soft-measurement operator is an instance
--   - encoding: "Define the matrix U = √(1 − F) + i√F. This is a unitary" (sentence before Eq. (8)) → unitarity stated as the first conjunct; reason: the same page's claim, kept with Eq. (8)
--   - encoding: Φ_F† the adjoint of the channel Φ_F → measChannel F, the formula √F X √F + √(1 − F) X √(1 − F); reason: p. 14, last line of the derivation of Eq. (8), gives this formula for Φ_F†; √F and √(1 − F) are Hermitian, so it is the adjoint
-- source:
--   Chen, O'Donnell, Pelecanos, Wright, Online Shadow Tomography Matching the Classical Bounds, STOC 2027 submission (manuscript of November 2, 2026, sha256 90993723…dc3a9), Eq. (8), p. 14 (with the preceding sentence on unitarity)

import Mathlib
import Definitions.Def_ShadowTomography_UpperBound_IsEffect
import Definitions.Def_OnlineShadow_LogRate_measChannel

open scoped Matrix ComplexOrder

namespace OnlineShadow.LogRate

/-- **Eq. (8)** (Chen, O'Donnell, Pelecanos, Wright, *Online Shadow Tomography Matching the Classical Bounds*, STOC 2027 submission (manuscript of November 2, 2026, sha256 90993723…dc3a9), p.14). For an effect `0 ⪯ F ⪯ 1`, the matrix `U = √(1 − F) + i√F` is unitary, and
for every operator `X` the post-measurement channel satisfies `Φ_F†(X) = (1/2)(U†XU + UXU†)`.

**Formalization Note** `Φ_F†(X) = √F X √F + √(1 − F) X √(1 − F)` is `measChannel F X` (the channel is
self-adjoint). The unitarity is the sentence preceding Eq. (8) on the same page. Square roots are
`cfc Real.sqrt`; operators are matrices over a finite index type. -/
theorem eq_8 {ι : Type} [Fintype ι] [DecidableEq ι] (F : Matrix ι ι ℂ)
    (hF : ShadowTomography.UpperBound.IsEffect F) :
    let U := cfc Real.sqrt (1 - F) + Complex.I • cfc Real.sqrt F
    U ∈ Matrix.unitaryGroup ι ℂ ∧
      ∀ X : Matrix ι ι ℂ, measChannel F X = (1 / 2 : ℂ) • (Uᴴ * X * U + U * X * Uᴴ) := by sorry

end OnlineShadow.LogRate
