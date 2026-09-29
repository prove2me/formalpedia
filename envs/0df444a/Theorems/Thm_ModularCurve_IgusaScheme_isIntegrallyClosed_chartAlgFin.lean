-- Prove2me | Theorems.Thm_ModularCurve_IgusaScheme_isIntegrallyClosed_chartAlgFin
-- name    : ModularCurve.IgusaScheme.isIntegrallyClosed_chartAlgFin
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.721416+00:00
-- url     : https://prove2.me/theorems/663ea5ff-e8d9-50fe-9a8b-a637238350b0
-- title:
--   The j-finite Igusa chart ring is integrally closed
-- statement:
--   Let $N$ be a natural number with $N \neq 0$ and let $\ell$ be a prime. Write $\mathbb{Z}_\ell$ for the coefficient ring [`GaloisRep.ratLocalizedAt ℓ`](def/GaloisRep_Flat.html#L8) and $F$ for the field `modularFunctionFieldFull N`, viewed as a $\mathbb{Z}_\ell$-algebra, and let $j =$ `jFull N` be the element of $F$ given by the modular function `jq` together with its membership in the full modular function field. By definition `chartAlgFin N ℓ` is `chartAlg N ℓ {jFull N}`, the $\mathbb{Z}_\ell$-subalgebra of $F$ whose elements are exactly those $x \in F$ that are integral over the $\mathbb{Z}_\ell$-subalgebra $\mathbb{Z}_\ell[j] =$ `Algebra.adjoin ℤℓ {jFull N}` of $F$; thus `chartAlgFin N ℓ` is the integral closure of $\mathbb{Z}_\ell[j]$ in $F$. The assertion is that the ring `chartAlgFin N ℓ`, regarded as a commutative ring in its own right, satisfies `IsIntegrallyClosed`: every element of its fraction field that is integral over it already lies in its image, i.e. it is an integrally closed domain.
--
--   This is the normality of the affine chart of the Igusa scheme [`ModularCurve.IgusaScheme`](def/ModularCurve_IgusaScheme.html#L255) (the pushout of `fFin N ℓ` and `fInf N ℓ`) attached to the finite part of the $j$-line: the integral closure of $\mathbb{Z}_\ell[j]$ in the full modular function field is integrally closed. It feeds the reducedness and base-change statements for this chart, among them [`ModularCurve.IgusaScheme.isIntegrallyClosed_tensor_chartAlgFin_of_charZero`](thm.html#ModularCurve.IgusaScheme.isIntegrallyClosed_tensor_chartAlgFin_of_charZero), [`ModularCurve.IgusaScheme.isReduced_chartAlgFin_tensor`](thm.html#ModularCurve.IgusaScheme.isReduced_chartAlgFin_tensor) and [`ModularCurve.IgusaScheme.isReduced_chartAlgInf_tensor`](thm.html#ModularCurve.IgusaScheme.isReduced_chartAlgInf_tensor).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_IgusaScheme_isIntegrallyClosed_chartAlgFin.lean

import Mathlib
import Definitions.Def_ModularCurve_IgusaScheme

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve ModularCurve.IgusaScheme

theorem ModularCurve.IgusaScheme.isIntegrallyClosed_chartAlgFin (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime] :
    IsIntegrallyClosed ↥(chartAlgFin N ℓ) := by sorry
