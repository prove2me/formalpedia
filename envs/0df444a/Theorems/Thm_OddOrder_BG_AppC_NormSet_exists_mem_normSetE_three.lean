-- Prove2me | Theorems.Thm_OddOrder_BG_AppC_NormSet_exists_mem_normSetE_three
-- name    : OddOrder.BG.AppC.NormSet.exists_mem_normSetE_three
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T04:47:15.550944+00:00
-- url     : https://prove2.me/theorems/d8800fd5-fad3-4b76-a52e-67589c6aac18
-- title:
--   BG Lemma C.2 ($q=3$): the norm set contains an element $a\ne1$
-- statement:
--   Let $p$ be an odd prime. Then there is an element $a\in\mathbb{F}_{p^3}$ with $a\ne1$ and
--   $$a\in E=\{x\in\mathbb{F}_{p^3}: N(x)=N(2-x)=1\},$$
--   where $N(x)=x\cdot x^{p}\cdot x^{p^2}$ is the norm to $\mathbb{F}_p$.
--
--   This is the lifting step of Lemma C.2 of Bender--Glauberman Appendix C in the case $q=3$: a root-free polynomial $f_c$ yields an element of $E$ different from $1$ (its Frobenius conjugates give $N(a)=N(2-a)=1$).
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/AppC_NormSet.lean#L795-L901

import Definitions.Def_OddOrder_BG_AppC_NormSetBasic
import Definitions.Def_OddOrder_BG_AppC_NormSet
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

theorem exists_mem_normSetE_three [Fact p.Prime] (hpodd : Odd p) :
    ∃ a : GaloisField p 3, a ∈ normSetE p 3 ∧ a ≠ 1 := by sorry

end OddOrder.BG.AppC.NormSet
