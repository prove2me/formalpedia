-- Prove2me | Theorems.Thm_OnlineShadow_LogRate_lemma_4_8
-- name    : OnlineShadow.LogRate.lemma_4_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T04:04:21.773739+00:00
-- url     : https://prove2.me/theorems/9cf261bf-7445-4eb3-b80d-7620334f7cb5
-- title:
--   Lemma 4.8 — damage of a unitary close to $1$ in the $F$-norm
-- statement:
--   Let $F$ be a Hermitian operator on a finite-dimensional space with $f_-1\preceq F\preceq f_+1$ for constants $0<f_-\le f_+\le1$. Let $U$ be a unitary commuting with $F$ such that $(U-1)^\dagger(U-1)\preceq aF$ for some $a\ge0$.
--
--   **Lemma 4.8.** For every Hermitian observable $0\preceq X\preceq1$,
--   $$\frac12\big(U^\dagger XU+UXU^\dagger\big)-X\preceq a\Big(1+\sqrt{\tfrac{f_+}{f_-}}\Big)F .$$
--
--   This is the per-block operator inequality from which Lemma 4.9 bounds how much a soft measurement increases the number operator.
--
--   **Formalization Note** Operators are complex matrices over a finite index type; $0\preceq X\preceq1$ is positive semidefiniteness of $X$ and of $1-X$.
--
--   Differences from the source:
--   - encoding: operators on a finite-dimensional Hilbert space → complex matrices over a finite index type ι; reason: the same objects
--   - encoding: a Hermitian operator F with f₋1 ⪯ F ⪯ f₊1 → no separate Hermitian hypothesis on F; reason: f₋1 ⪯ F (F − f₋1 positive semidefinite) already makes F Hermitian
-- source:
--   Chen, O'Donnell, Pelecanos, Wright, Online Shadow Tomography Matching the Classical Bounds, STOC 2027 submission (manuscript of November 2, 2026, sha256 90993723…dc3a9), Lemma 4.8, p. 15

import Mathlib

open scoped Matrix ComplexOrder

namespace OnlineShadow.LogRate

/-- **Lemma 4.8** (Chen, O'Donnell, Pelecanos, Wright, *Online Shadow Tomography Matching the Classical Bounds*, STOC 2027 submission (manuscript of November 2, 2026, sha256 90993723…dc3a9), p.15). Let `0 < f₋ ≤ f₊ ≤ 1` and let `F` be a Hermitian operator with
`f₋1 ⪯ F ⪯ f₊1`. Let `U` be a unitary commuting with `F` with `(U − 1)†(U − 1) ⪯ aF` for some
`a ≥ 0`. Then for every Hermitian `0 ⪯ X ⪯ 1`,
`(1/2)(U†XU + UXU†) − X ⪯ a(1 + √(f₊/f₋)) F`.

**Formalization Note** Operators are matrices over a finite index type `ι`; `X ⪯ Y` is
`(Y − X).PosSemidef`; `0 ⪯ X ⪯ 1` is `X.PosSemidef ∧ (1 − X).PosSemidef` (which makes `X` Hermitian).
That `F` is Hermitian follows from `f₋1 ⪯ F` and is not a separate hypothesis. -/
theorem lemma_4_8 {ι : Type} [Fintype ι] [DecidableEq ι] (F U X : Matrix ι ι ℂ) (fm fp a : ℝ)
    (hfm : 0 < fm) (hfmp : fm ≤ fp) (hfp : fp ≤ 1)
    (hFlo : (F - ((fm : ℝ) : ℂ) • (1 : Matrix ι ι ℂ)).PosSemidef)
    (hFhi : (((fp : ℝ) : ℂ) • (1 : Matrix ι ι ℂ) - F).PosSemidef)
    (hU : U ∈ Matrix.unitaryGroup ι ℂ) (hUF : U * F = F * U) (ha : 0 ≤ a)
    (hUa : (((a : ℝ) : ℂ) • F - (U - 1)ᴴ * (U - 1)).PosSemidef)
    (hX0 : X.PosSemidef) (hX1 : (1 - X).PosSemidef) :
    ((((a * (1 + Real.sqrt (fp / fm)) : ℝ)) : ℂ) • F -
      ((1 / 2 : ℂ) • (Uᴴ * X * U + U * X * Uᴴ) - X)).PosSemidef := by sorry

end OnlineShadow.LogRate
