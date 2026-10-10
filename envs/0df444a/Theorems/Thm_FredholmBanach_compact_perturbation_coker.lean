-- Prove2me | Theorems.Thm_FredholmBanach_compact_perturbation_coker
-- name    : FredholmBanach.compact_perturbation_coker
-- status  : Open
-- author  : @Mazecto
-- created : 2026-10-09T15:40:28.631847+00:00
-- url     : https://prove2.me/theorems/4f04abf9-e1b6-4b46-a43e-b3358061ea3c
-- title:
--   A range of finite codimension stays closed and of finite codimension under compact perturbations
-- statement:
--   Let $\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$ and let $E$, $F$ be Banach spaces over $\mathbb{K}$. Let $u,h:E\to F$ be bounded linear maps. Assume $F/\operatorname{Im}u$ is finite-dimensional and $h$ is compact (it maps some neighbourhood of $0$ into a compact set). Then $F/\operatorname{Im}(u+h)$ is finite-dimensional and $\operatorname{Im}(u+h)$ is closed in $F$.
-- source:
--   N. Bourbaki, Théories spectrales, Chapitres III à V, Springer (2023), https://doi.org/10.1007/978-3-031-19505-1, Chapitre III, § 5, n° 2, Théorème 2, p. TS III.73 (stated there for Fréchet spaces)

import Definitions.Def_FredholmBanach_Setting

namespace FredholmBanach

open Topology

/-- Bourbaki, *Théories spectrales*, III, § 5, n° 2, Théorème 2 (TS III.73), for Banach spaces:
if the range of `u` has finite codimension and `h` is compact, then the range of `u + h` is
closed and of finite codimension. -/
theorem compact_perturbation_coker {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
    {u h : E →L[𝕜] F} (hc : FiniteDimensional 𝕜 (F ⧸ u.range)) (hh : IsCompactOperator h) :
    FiniteDimensional 𝕜 (F ⧸ (u + h).range) ∧ IsClosed ((u + h).range : Set F) := by sorry

end FredholmBanach
