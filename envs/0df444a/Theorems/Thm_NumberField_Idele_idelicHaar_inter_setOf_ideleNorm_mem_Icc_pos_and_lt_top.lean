-- Prove2me | Theorems.Thm_NumberField_Idele_idelicHaar_inter_setOf_ideleNorm_mem_Icc_pos_and_lt_top
-- name    : NumberField.Idele.idelicHaar_inter_setOf_ideleNorm_mem_Icc_pos_and_lt_top
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/b212beed-7ba3-516c-8a45-7a6d71272008
-- title:
--   Positive finite volume of norm slabs in a fundamental domain
-- statement:
--   Let $K$ be a number field, and equip the group of units $(\mathbb{A}_K^\times) = (\mathrm{AdeleRing}(\mathcal{O}_K,K))^\times$ of the adele ring with the Borel $\sigma$-algebra `ideleBorel` coming from its topology, together with the measure `idelicHaar`, which is the Haar measure `Measure.haar` on this group. Let $D$ be a measurable subset of $(\mathbb{A}_K^\times)$ which is a fundamental domain, in the sense of `MeasureTheory.IsFundamentalDomain` with respect to `idelicHaar`, for the action of the subgroup [`M4aHerbrand.principalIdeles`](def/M4aHerbrand_IdeleClassVocab.html#L16) $(\mathcal{O}_K, K)$, i.e. the image of $K^\times$ under the map of unit groups induced by the structure morphism $K \to \mathbb{A}_K$. Let $a, b$ be real numbers with $0 < a$ and $a < b$. Then the `idelicHaar` measure of the set $D \cap \{z : \mathrm{ideleNorm}\,K\,z \in [a,b]\}$, where $\mathrm{ideleNorm}\,K\,z$ is the real number obtained from the distributive Haar character $\mathrm{distribHaarChar}(\mathbb{A}_K)(z) \in \mathbb{R}_{\ge 0}$ of the scaling action of $z$ on the adele ring, is both strictly positive and strictly less than $\top$ in $[0,\infty]$.
--
--   This is the statement, in the form needed for slab integrals, that the norm-one idele class group has finite positive volume: intersecting any measurable fundamental domain for $K^\times$ acting on $\mathbb{A}_K^\times$ with a closed norm slab $a \le \lVert z\rVert \le b$ yields a set of positive finite Haar measure. It feeds the growth and averaging estimates for class sums and for invariant band-supported functions in the adelic automorphic-form apparatus.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_Idele_idelicHaar_inter_setOf_ideleNorm_mem_Icc_pos_and_lt_top.lean

import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_NumberField_TateGlobalZeta
import Mathlib.MeasureTheory.Group.FundamentalDomain

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField
open NumberField.TateGlobal
open scoped ENNReal

attribute [local instance] NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

theorem NumberField.Idele.idelicHaar_inter_setOf_ideleNorm_mem_Icc_pos_and_lt_top
    (K : Type) [Field K] [NumberField K]
    (D : Set (AdeleRing (𝓞 K) K)ˣ) (hD : MeasurableSet D)
    (hDF : IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 K) K) D (NumberField.Idele.idelicHaar K))
    (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    0 < (NumberField.Idele.idelicHaar K) (D ∩ {z | ideleNorm K z ∈ Set.Icc a b}) ∧
      (NumberField.Idele.idelicHaar K) (D ∩ {z | ideleNorm K z ∈ Set.Icc a b}) < ⊤ := by sorry
