-- Prove2me | Theorems.Thm_OddOrder_BG_AppC_NormSet_normOneFrobenius_error_separation_of_five_le
-- name    : OddOrder.BG.AppC.NormSet.normOneFrobenius_error_separation_of_five_le
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T07:39:26.161021+00:00
-- url     : https://prove2.me/theorems/c74c6e94-9e5b-496f-bbdd-b44471f57473
-- title:
--   BG Lemma C.2: numerical error separation for $q\ge5$
-- statement:
--   Let $p$ be a prime and $q\ge5$ a natural number, and let $U$ be the group of norm-one units of $\mathbb{F}_{p^q}$ (units whose norm to $\mathbb{F}_p$ is $1$). Then for every natural number $c\le|U|$,
--   $$|U|\cdot p^{q}\sqrt{p^{q}}<\bigl\|\,|U|^{3}-c\,p^{q}\,\bigr\|,$$
--   where the norm on the right is the absolute value of the complex number $|U|^3-c\,p^q$.
--
--   This is the purely numerical input for the class-sum bridge in Lemma C.2 of Bender--Glauberman Appendix C: the error bound for non-kernel terms is separated from every possible coefficient $c\le|U|$.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/AppC_NormOneInduce.lean#L120-L194

import Definitions.Def_OddOrder_BG_AppC_NormSet
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_ClassSumAlgebra
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_ColumnOrthogonality
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_InducedIrreducible
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_InflationCharacter
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_LinearCharacter
import Definitions.Def_OddOrder_Isaacs_Ch06_FrobeniusActions_FrobeniusGroup
import Definitions.Def_OddOrder_Mathlib_SemidirectProduct
import Definitions.Def_OddOrder_Peterfalvi_S08_CoherenceTheorems
import Definitions.Def_OddOrder_BG_AppC_NormOneInduce
import Mathlib.Data.Set.Card.Arithmetic

namespace OddOrder.BG.AppC.NormSet

open OddOrder.RepresentationTheory

open scoped commutatorElement

variable (p q : ℕ)

theorem normOneFrobenius_error_separation_of_five_le [Fact p.Prime] (hq : 5 ≤ q) :
    ∀ c : ℕ, c ≤ Nat.card (normOneUnits p q) →
      (Nat.card (normOneUnits p q) : ℝ) *
          (((p ^ q : ℕ) : ℝ) * √(((p ^ q : ℕ) : ℝ))) <
        ‖((Nat.card (normOneUnits p q) : ℂ) ^ 3 -
          (c : ℂ) * ((p ^ q : ℕ) : ℂ))‖ := by sorry

end OddOrder.BG.AppC.NormSet
