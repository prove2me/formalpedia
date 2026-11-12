-- Prove2me | Theorems.Thm_OddOrder_BG_AppC_FieldNormalizerData_exists_step4C5NormalForms
-- name    : OddOrder.BG.AppC.FieldNormalizerData.exists_step4C5NormalForms
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T05:26:29.695423+00:00
-- url     : https://prove2.me/theorems/60a221cb-00cf-444f-bd3a-e1b4f8e4b689
-- title:
--   BG Appendix C: the three (C.5) factors admit compatible normal forms
-- statement:
--   Let `data : FieldNormalizerData p q G` be the field-normalizer data of Bender--Glauberman Appendix C, and let $a,b$ be norm-one units of $\mathbb{F}_{p^q}$. Then the type `Step4C5NormalForms data a b` is nonempty: the three factors in relation (C.4) (the factors called (C.5)) admit Step 1 normal forms $\sigma(u_i)\,\sigma(c_i)\,\sigma(v_i)$ ($c_i\in\mathbb{Z}/p$, $u_i,v_i$ norm-one units) together with compatible readings of their right complement components modulo $P$.
--
--   This existence statement supplies the normal forms to which the later steps of Lemma C.3 (such as (C.6), (C.7), (C.9)) are applied.
--
--   **Formalization Note** Nonemptiness is stated as `Nonempty (Step4C5NormalForms data a b)`; the structure records the coordinates, units, the three normal-form equations and the right-component identities.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/AppC_LemmaC3_NormalForms.lean#L244-L296

import Definitions.Def_OddOrder_BG_AppC_LemmaC3_ScalarCalculus
import Definitions.Def_OddOrder_BG_AppC_LemmaC3_NormalForms

namespace OddOrder.BG.AppC

open OddOrder.GroupTheory

open scoped Pointwise

open scoped BigOperators

variable {p q : ℕ} [Fact p.Prime] {G : Type*} [Group G]

namespace FieldNormalizerData

section Step4

theorem exists_step4C5NormalForms
    (data : FieldNormalizerData p q G)
    (a b : NormSet.normOneUnits p q) :
    Nonempty (Step4C5NormalForms data a b) := by sorry

end Step4

end FieldNormalizerData

end OddOrder.BG.AppC
