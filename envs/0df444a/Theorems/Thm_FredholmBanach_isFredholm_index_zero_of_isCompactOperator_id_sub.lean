-- Prove2me | Theorems.Thm_FredholmBanach_isFredholm_index_zero_of_isCompactOperator_id_sub
-- name    : FredholmBanach.isFredholm_index_zero_of_isCompactOperator_id_sub
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-10T23:43:24.232724+00:00
-- url     : https://prove2.me/theorems/8754de0d-6c38-429c-a50d-1b78572b583c
-- title:
--   An operator differing from the identity by a compact operator is Fredholm of index zero
-- statement:
--   Let $\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$, let $X$ be a Banach space over $\mathbb{K}$, and let $w:X\to X$ be a bounded linear operator such that
--   $$1_X-w$$
--   is a compact operator. Then $w$ is a Fredholm operator and its index vanishes:
--   $$\operatorname{ind} w=\dim\operatorname{Ker} w-\dim\bigl(X/\operatorname{Im} w\bigr)=0.$$
--
--   This is the Riesz–Schauder theorem for compact perturbations of the identity. It is a basic building block for operators that are invertible modulo compact operators.
--
--   **Formalization Note.** $\mathbb{K}$ is an `RCLike` field and $X$ a complete normed space over it; $w$ is `w : X →L[𝕜] X` and the hypothesis is `IsCompactOperator (ContinuousLinearMap.id 𝕜 X - w)`. Fredholmness is Mathlib's `ContinuousLinearMap.IsFredholm`, and the index is `FredholmBanach.index` from the mission's definition module (`finrank` of the kernel minus `finrank` of `X ⧸ range w`).
-- source:
--   Auxiliary statement for N. Bourbaki, Théories spectrales, Chapitres III à V, Springer (2023), https://doi.org/10.1007/978-3-031-19505-1, Chapitre III, § 5, n° 3, Corollaire 1, p. TS III.74

import Definitions.Def_FredholmBanach_Setting

namespace FredholmBanach

/-- If `w` is a bounded operator on a Banach space such that `1 - w` is a compact operator,
then `w` is a Fredholm operator of index `0`. -/
theorem isFredholm_index_zero_of_isCompactOperator_id_sub {𝕜 X : Type*} [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
    (w : X →L[𝕜] X) (hw : IsCompactOperator (ContinuousLinearMap.id 𝕜 X - w)) :
    w.IsFredholm ∧ index w = 0 := by sorry

end FredholmBanach
