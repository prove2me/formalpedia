-- Prove2me | Theorems.Thm_FredholmBanach_exists_equiv_of_index_eq_zero
-- name    : FredholmBanach.exists_equiv_of_index_eq_zero
-- status  : Open
-- author  : @Mazecto
-- created : 2026-10-09T15:39:39.283243+00:00
-- url     : https://prove2.me/theorems/56591899-7687-488c-96de-1e899abcf640
-- title:
--   An injective or surjective Fredholm operator of index zero is an isomorphism
-- statement:
--   Let $\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$ and let $E$, $F$ be Banach spaces over $\mathbb{K}$. Let $u:E\to F$ be a Fredholm operator with $\operatorname{ind}u=0$, where $\operatorname{ind}u=\dim\operatorname{Ker}u-\dim(F/\operatorname{Im}u)$. If $u$ is injective or surjective, then $u$ is an isomorphism of Banach spaces: there is a continuous linear equivalence $e:E\to F$ (bijective, with continuous inverse) whose underlying map is $u$.
-- source:
--   N. Bourbaki, Théories spectrales, Chapitres III à V, Springer (2023), https://doi.org/10.1007/978-3-031-19505-1, Chapitre III, § 3, n° 3, p. TS III.44

import Definitions.Def_FredholmBanach_Setting

namespace FredholmBanach

open Topology

/-- Bourbaki, *Théories spectrales*, III, § 3, n° 3 (TS III.44): a Fredholm operator of index
`0` that is injective or surjective is an isomorphism of topological vector spaces. -/
theorem exists_equiv_of_index_eq_zero {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
    {u : E →L[𝕜] F} (hu : u.IsFredholm) (h0 : index u = 0)
    (h : Function.Injective u ∨ Function.Surjective u) :
    ∃ e : E ≃L[𝕜] F, (e : E →L[𝕜] F) = u := by sorry

end FredholmBanach
