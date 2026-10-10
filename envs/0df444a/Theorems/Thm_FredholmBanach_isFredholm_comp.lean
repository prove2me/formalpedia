-- Prove2me | Theorems.Thm_FredholmBanach_isFredholm_comp
-- name    : FredholmBanach.isFredholm_comp
-- status  : Open
-- author  : @Mazecto
-- created : 2026-10-09T15:38:38.283296+00:00
-- url     : https://prove2.me/theorems/72f7cc95-e086-4383-b411-5d149906f8dc
-- title:
--   The composition of two Fredholm operators is Fredholm
-- statement:
--   Let $\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$ and let $E$, $F$, $G$ be Banach spaces over $\mathbb{K}$. If $u:E\to F$ and $v:F\to G$ are Fredholm operators, then $v\circ u:E\to G$ is a Fredholm operator.
-- source:
--   N. Bourbaki, Théories spectrales, Chapitres III à V, Springer (2023), https://doi.org/10.1007/978-3-031-19505-1, Chapitre III, § 3, n° 2, Remarque 2, p. TS III.41

import Definitions.Def_FredholmBanach_Setting

namespace FredholmBanach

open Topology

/-- Bourbaki, *Théories spectrales*, III, § 3, n° 2, Remarque 2 (TS III.41): the composition
of two Fredholm operators is Fredholm. -/
theorem isFredholm_comp {𝕜 E F G : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
    [NormedAddCommGroup G] [NormedSpace 𝕜 G] [CompleteSpace G]
    {u : E →L[𝕜] F} {v : F →L[𝕜] G} (hu : u.IsFredholm) (hv : v.IsFredholm) :
    (v.comp u).IsFredholm := by sorry

end FredholmBanach
