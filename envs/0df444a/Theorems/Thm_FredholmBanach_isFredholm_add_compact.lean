-- Prove2me | Theorems.Thm_FredholmBanach_isFredholm_add_compact
-- name    : FredholmBanach.isFredholm_add_compact
-- status  : Open
-- author  : @Mazecto
-- created : 2026-10-09T15:40:41.535349+00:00
-- url     : https://prove2.me/theorems/ec20b8e9-8d2f-4e2c-a868-9c495cace274
-- title:
--   Compact perturbations preserve the Fredholm property and the index
-- statement:
--   Let $\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$ and let $E$, $F$ be Banach spaces over $\mathbb{K}$. Let $u:E\to F$ be a Fredholm operator and let $h:E\to F$ be a compact operator (it maps some neighbourhood of $0$ into a compact set). Then $u+h$ is a Fredholm operator and $\operatorname{ind}(u+h)=\operatorname{ind}u$, where $\operatorname{ind}u=\dim\operatorname{Ker}u-\dim(F/\operatorname{Im}u)$.
-- source:
--   N. Bourbaki, Théories spectrales, Chapitres III à V, Springer (2023), https://doi.org/10.1007/978-3-031-19505-1, Chapitre III, § 5, n° 3, Théorème 3, p. TS III.73

import Definitions.Def_FredholmBanach_Setting

namespace FredholmBanach

open Topology

/-- Bourbaki, *Théories spectrales*, III, § 5, n° 3, Théorème 3 (TS III.73), for Banach spaces:
if `u` is Fredholm and `h` is compact, then `u + h` is Fredholm and `ind (u + h) = ind u`. -/
theorem isFredholm_add_compact {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
    {u h : E →L[𝕜] F} (hu : u.IsFredholm) (hh : IsCompactOperator h) :
    (u + h).IsFredholm ∧ index (u + h) = index u := by sorry

end FredholmBanach
