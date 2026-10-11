-- Prove2me | Theorems.Thm_FredholmBanach_isCompactOperator_of_finiteDimensional_range
-- name    : FredholmBanach.isCompactOperator_of_finiteDimensional_range
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-10T23:36:45.656519+00:00
-- url     : https://prove2.me/theorems/3f731a29-6713-4d46-b882-e62aba1948be
-- title:
--   Bounded operators of finite rank are compact
-- statement:
--   Let $\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$, let $E$ and $F$ be normed spaces over $\mathbb{K}$, and let $h:E\to F$ be a bounded linear map whose range $\operatorname{Im}h$ is finite-dimensional. Then $h$ is a compact operator: it maps some neighbourhood of $0$ into a compact subset of $F$.
--
--   Operators of finite rank are thus a special case of compact operators, so any statement about compact perturbations applies in particular to finite-rank perturbations.
--
--   **Formalization Note.** $\mathbb{K}$ is an `RCLike` field, $E$ and $F$ are normed spaces over it (no completeness assumed), and $h$ is `h : E →L[𝕜] F`. The range is `h.range`, the hypothesis is `FiniteDimensional 𝕜 h.range`, and compactness is Mathlib's `IsCompactOperator h` (there is a compact set $K$ with $h^{-1}(K)$ a neighbourhood of $0$).
-- source:
--   Auxiliary statement for N. Bourbaki, Théories spectrales, Chapitres III à V, Springer (2023), https://doi.org/10.1007/978-3-031-19505-1, Chapitre III, § 5, n° 3, Corollaire 2, p. TS III.74

import Definitions.Def_FredholmBanach_Setting

namespace FredholmBanach

/-- A bounded linear map between normed spaces whose range is finite-dimensional is a compact
operator. -/
theorem isCompactOperator_of_finiteDimensional_range {𝕜 E F : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (h : E →L[𝕜] F) (hh : FiniteDimensional 𝕜 h.range) :
    IsCompactOperator h := by sorry

end FredholmBanach
