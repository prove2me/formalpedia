-- Prove2me | Theorems.Thm_FredholmBanach_isClosed_range_of_finiteDimensional_coker
-- name    : FredholmBanach.isClosed_range_of_finiteDimensional_coker
-- status  : Open
-- author  : @Mazecto
-- created : 2026-10-09T15:37:56.104827+00:00
-- url     : https://prove2.me/theorems/16b3d31b-fe6c-47fb-94cb-35bd7fa73022
-- title:
--   A bounded operator between Banach spaces whose range has finite codimension has closed range
-- statement:
--   Let $\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$ and let $E$, $F$ be Banach spaces over $\mathbb{K}$. Let $u:E\to F$ be a bounded linear map such that the quotient $F/\operatorname{Im}u$ is finite-dimensional. Then $\operatorname{Im}u$ is closed in $F$, and $u$ is a strict map: the induced bijection $E/\operatorname{Ker}u\to\operatorname{Im}u$ is a homeomorphism.
-- source:
--   N. Bourbaki, Théories spectrales, Chapitres III à V, Springer (2023), https://doi.org/10.1007/978-3-031-19505-1, Chapitre III, § 3, n° 5, Lemme 6, p. TS III.52 (stated there for Fréchet spaces)

import Definitions.Def_FredholmBanach_Setting

namespace FredholmBanach

open Topology

/-- Bourbaki, *Théories spectrales*, III, § 3, n° 5, Lemme 6 (TS III.52), for Banach spaces:
if the range of `u` has finite codimension, then it is closed and `u` is a strict map. -/
theorem isClosed_range_of_finiteDimensional_coker {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
    (u : E →L[𝕜] F) (hu : FiniteDimensional 𝕜 (F ⧸ u.range)) :
    IsClosed (u.range : Set F) ∧ IsStrictMap u := by sorry

end FredholmBanach
