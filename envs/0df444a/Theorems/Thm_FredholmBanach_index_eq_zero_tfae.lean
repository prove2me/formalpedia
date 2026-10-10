-- Prove2me | Theorems.Thm_FredholmBanach_index_eq_zero_tfae
-- name    : FredholmBanach.index_eq_zero_tfae
-- status  : Open
-- author  : @Mazecto
-- created : 2026-10-09T15:40:59.549224+00:00
-- url     : https://prove2.me/theorems/764cb104-f3b4-4181-99ae-d157fafdd364
-- title:
--   Fredholm operators of index zero are the finite-rank and the compact perturbations of isomorphisms
-- statement:
--   Let $\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$ and let $E$, $F$ be Banach spaces over $\mathbb{K}$. For a bounded linear map $u:E\to F$ the following are equivalent:
--
--   1. $u$ is a Fredholm operator and $\operatorname{ind}u=0$, where $\operatorname{ind}u=\dim\operatorname{Ker}u-\dim(F/\operatorname{Im}u)$;
--   2. there is an isomorphism $e:E\to F$ (a continuous linear bijection with continuous inverse) such that $u-e$ has finite-dimensional range;
--   3. there is an isomorphism $e:E\to F$ such that $u-e$ is a compact operator.
-- source:
--   N. Bourbaki, Théories spectrales, Chapitres III à V, Springer (2023), https://doi.org/10.1007/978-3-031-19505-1, Chapitre III, § 5, n° 3, Corollaire 2, pp. TS III.74–III.75 (stated there for separated locally convex spaces)

import Definitions.Def_FredholmBanach_Setting

namespace FredholmBanach

open Topology

/-- Bourbaki, *Théories spectrales*, III, § 5, n° 3, Corollaire 2 (TS III.74), for Banach spaces:
the following are equivalent: `u` is Fredholm of index `0`; `u` differs from an isomorphism
`E ≃L[𝕜] F` by an operator of finite rank; `u` differs from an isomorphism by a compact
operator. -/
theorem index_eq_zero_tfae {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
    (u : E →L[𝕜] F) :
    [u.IsFredholm ∧ index u = 0,
      ∃ e : E ≃L[𝕜] F, FiniteDimensional 𝕜 (u - (e : E →L[𝕜] F)).range,
      ∃ e : E ≃L[𝕜] F, IsCompactOperator (u - (e : E →L[𝕜] F))].TFAE := by sorry

end FredholmBanach
