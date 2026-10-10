-- Prove2me | Theorems.Thm_FredholmBanach_isOpen_isFredholm_index_locallyConstant
-- name    : FredholmBanach.isOpen_isFredholm_index_locallyConstant
-- status  : Open
-- author  : @Mazecto
-- created : 2026-10-09T15:39:58.460601+00:00
-- url     : https://prove2.me/theorems/7add8fea-6932-421a-8ad2-45eefcd6463b
-- title:
--   Fredholm operators form an open set on which the index is locally constant
-- statement:
--   Let $\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$ and let $E$, $F$ be Banach spaces over $\mathbb{K}$. Give the space $\mathcal{L}(E;F)$ of bounded linear maps $E\to F$ the operator-norm topology. Then:
--
--   1. the set of Fredholm operators $E\to F$ is open in $\mathcal{L}(E;F)$;
--   2. every Fredholm operator $u$ has a neighbourhood in $\mathcal{L}(E;F)$ on which $\operatorname{ind}v=\operatorname{ind}u$, where $\operatorname{ind}u=\dim\operatorname{Ker}u-\dim(F/\operatorname{Im}u)$.
-- source:
--   N. Bourbaki, Théories spectrales, Chapitres III à V, Springer (2023), https://doi.org/10.1007/978-3-031-19505-1, Chapitre III, § 4, n° 2, Théorème 1, p. TS III.58

import Definitions.Def_FredholmBanach_Setting

namespace FredholmBanach

open Topology

/-- Bourbaki, *Théories spectrales*, III, § 4, n° 2, Théorème 1 (TS III.58): the set of Fredholm
operators is open in `L(E; F)`, and the index is locally constant on it. -/
theorem isOpen_isFredholm_index_locallyConstant {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F] :
    IsOpen {u : E →L[𝕜] F | u.IsFredholm} ∧
      ∀ u : E →L[𝕜] F, u.IsFredholm → ∀ᶠ v in 𝓝 u, index v = index u := by sorry

end FredholmBanach
