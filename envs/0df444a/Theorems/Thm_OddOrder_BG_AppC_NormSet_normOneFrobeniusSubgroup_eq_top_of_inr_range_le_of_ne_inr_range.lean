-- Prove2me | Theorems.Thm_OddOrder_BG_AppC_NormSet_normOneFrobeniusSubgroup_eq_top_of_inr_range_le_of_ne_inr_range
-- name    : OddOrder.BG.AppC.NormSet.normOneFrobeniusSubgroup_eq_top_of_inr_range_le_of_ne_inr_range
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T04:44:43.26529+00:00
-- url     : https://prove2.me/theorems/1fe0852c-75b6-465c-a1df-f8518b030b10
-- title:
--   BG Lemma C.3, Step 3: a subgroup of $P\rtimes U$ properly containing $U$ is everything
-- statement:
--   Let $p$ be a prime and $q$ a prime number, and assume $\gcd\bigl(\tfrac{p^q-1}{p-1},\,p-1\bigr)=1$. Let $H=P\rtimes U$ be the group `normOneFrobeniusGroup p q` (the additive group of $\mathbb{F}_{p^q}$ extended by the norm-one units $U$), and let $X\le H$ be a subgroup containing the complement $U$ (the image of `SemidirectProduct.inr`) with $X\ne U$. Then
--   $$X=H.$$
--
--   This is the subgroup dichotomy of Step 3 of Lemma C.3 in Bender--Glauberman Appendix C: any subgroup containing $U$ is either $U$ or all of $PU$.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/AppC_NormSetBasic.lean#L944-L989

import Definitions.Def_OddOrder_BG_AppC_NormSetBasic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.Finite.Trace
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Algebra.Ring.AddAut
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Module.ZMod

namespace OddOrder.BG.AppC.NormSet

open scoped Pointwise

open Polynomial Finset

variable (p q : ℕ)

theorem normOneFrobeniusSubgroup_eq_top_of_inr_range_le_of_ne_inr_range
    [Fact p.Prime] (hq : q.Prime)
    (hA : Nat.Coprime ((p ^ q - 1) / (p - 1)) (p - 1))
    (X : Subgroup (normOneFrobeniusGroup p q))
    (hUle : (SemidirectProduct.inr : normOneUnits p q →* normOneFrobeniusGroup p q).range ≤ X)
    (hne : X ≠
      (SemidirectProduct.inr : normOneUnits p q →* normOneFrobeniusGroup p q).range) :
    X = ⊤ := by sorry

end OddOrder.BG.AppC.NormSet
