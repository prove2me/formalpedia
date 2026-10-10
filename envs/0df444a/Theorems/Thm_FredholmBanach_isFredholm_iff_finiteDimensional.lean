-- Prove2me | Theorems.Thm_FredholmBanach_isFredholm_iff_finiteDimensional
-- name    : FredholmBanach.isFredholm_iff_finiteDimensional
-- status  : Open
-- author  : @Mazecto
-- created : 2026-10-09T15:38:22.241343+00:00
-- url     : https://prove2.me/theorems/b635e960-921a-469a-8672-2110dc32c1a0
-- title:
--   Fredholm operators between Banach spaces are those with finite-dimensional kernel and cokernel
-- statement:
--   Let $\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$ and let $E$, $F$ be Banach spaces over $\mathbb{K}$. A bounded linear map $u:E\to F$ is Fredholm (in the sense of Mathlib's `ContinuousLinearMap.IsFredholm`) if and only if $\operatorname{Ker}u$ and $F/\operatorname{Im}u$ are finite-dimensional.
-- source:
--   N. Bourbaki, Théories spectrales, Chapitres III à V, Springer (2023), https://doi.org/10.1007/978-3-031-19505-1, Chapitre III, § 3, n° 5, Proposition 11, p. TS III.52 (stated there for Fréchet spaces)

import Definitions.Def_FredholmBanach_Setting

namespace FredholmBanach

open Topology

/-- Bourbaki, *Théories spectrales*, III, § 3, n° 5, Proposition 11 (TS III.52), for Banach
spaces: `u` is Fredholm if and only if its kernel and its cokernel `F ⧸ Im u` are
finite-dimensional. -/
theorem isFredholm_iff_finiteDimensional {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
    (u : E →L[𝕜] F) :
    u.IsFredholm ↔ FiniteDimensional 𝕜 u.ker ∧ FiniteDimensional 𝕜 (F ⧸ u.range) := by sorry

end FredholmBanach
