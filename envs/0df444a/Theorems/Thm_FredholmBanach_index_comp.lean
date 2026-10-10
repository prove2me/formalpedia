-- Prove2me | Theorems.Thm_FredholmBanach_index_comp
-- name    : FredholmBanach.index_comp
-- status  : Open
-- author  : @Mazecto
-- created : 2026-10-09T15:38:52.69886+00:00
-- url     : https://prove2.me/theorems/d8c52057-f6ba-462d-bd82-8693c490ce59
-- title:
--   The Fredholm index is additive under composition
-- statement:
--   Let $\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$ and let $E$, $F$, $G$ be Banach spaces over $\mathbb{K}$. If $u:E\to F$ and $v:F\to G$ are Fredholm operators, then
--   $$\operatorname{ind}(v\circ u)=\operatorname{ind}v+\operatorname{ind}u,$$
--   where $\operatorname{ind}u=\dim\operatorname{Ker}u-\dim(F/\operatorname{Im}u)$ and likewise for $v$ and $v\circ u$.
-- source:
--   N. Bourbaki, Théories spectrales, Chapitres III à V, Springer (2023), https://doi.org/10.1007/978-3-031-19505-1, Chapitre III, § 3, n° 3, formula (2), p. TS III.43

import Definitions.Def_FredholmBanach_Setting

namespace FredholmBanach

open Topology

/-- Bourbaki, *Théories spectrales*, III, § 3, n° 3, formula (2) (TS III.43): the index is
additive under composition, `ind (v ∘ u) = ind v + ind u`. -/
theorem index_comp {𝕜 E F G : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
    [NormedAddCommGroup G] [NormedSpace 𝕜 G] [CompleteSpace G]
    {u : E →L[𝕜] F} {v : F →L[𝕜] G} (hu : u.IsFredholm) (hv : v.IsFredholm) :
    index (v.comp u) = index v + index u := by sorry

end FredholmBanach
