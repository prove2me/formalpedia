-- Prove2me | Theorems.Thm_FredholmBanach_compact_perturbation_ker_range
-- name    : FredholmBanach.compact_perturbation_ker_range
-- status  : Open
-- author  : @Mazecto
-- created : 2026-10-09T15:40:13.066982+00:00
-- url     : https://prove2.me/theorems/694eee02-b39b-482b-9758-6f1f75466a6c
-- title:
--   Finite-dimensional kernel and closed range survive compact perturbations
-- statement:
--   Let $\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$ and let $E$, $F$ be Banach spaces over $\mathbb{K}$. Let $u,h:E\to F$ be bounded linear maps. Assume $\operatorname{Ker}u$ is finite-dimensional, $\operatorname{Im}u$ is closed in $F$, and $h$ is compact (it maps some neighbourhood of $0$ into a compact set). Then $\operatorname{Ker}(u+h)$ is finite-dimensional and $\operatorname{Im}(u+h)$ is closed in $F$.
-- source:
--   N. Bourbaki, Théories spectrales, Chapitres III à V, Springer (2023), https://doi.org/10.1007/978-3-031-19505-1, Chapitre III, § 5, n° 2, Théorème 1, p. TS III.72 (stated there for separated locally convex spaces and strict maps)

import Definitions.Def_FredholmBanach_Setting

namespace FredholmBanach

open Topology

/-- Bourbaki, *Théories spectrales*, III, § 5, n° 2, Théorème 1 (TS III.72), for Banach spaces:
if `u` has finite-dimensional kernel and closed range and `h` is compact, then `u + h` has
finite-dimensional kernel and closed range. -/
theorem compact_perturbation_ker_range {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
    {u h : E →L[𝕜] F} (hk : FiniteDimensional 𝕜 u.ker) (hr : IsClosed (u.range : Set F))
    (hh : IsCompactOperator h) :
    FiniteDimensional 𝕜 (u + h).ker ∧ IsClosed ((u + h).range : Set F) := by sorry

end FredholmBanach
