-- Prove2me | Theorems.Thm_OddOrder_BG_AppC_NormSet_lemmaC1
-- name    : OddOrder.BG.AppC.NormSet.lemmaC1
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T04:47:18.004223+00:00
-- url     : https://prove2.me/theorems/b5eab204-640b-4f2e-854b-333c12457dab
-- title:
--   BG Appendix C, Lemma C.1: if the norm set is inversion-closed with $\ge2$ elements, then $p\le q$
-- statement:
--   Let $p$ be a prime and $q$ a prime number, and let $E=\{a\in\mathbb{F}_{p^q}: N(a)=N(2-a)=1\}$ be the norm set, where $N(x)=\prod_{i<q}x^{p^i}$. Suppose $E=E^{-1}$ (as subsets of $\mathbb{F}_{p^q}$, with $E^{-1}$ the set of inverses) and $E$ has at least two elements. Then
--   $$p\le q.$$
--
--   For $a\in E\setminus\{1\}$ the map $\tau(a)=1/(2-a)$ sends $E$ to $E$, and the telescoping product gives $N((1-a)k+1)=1$ for all $k\in\mathbb{F}_p$. The degree-$q$ polynomial $\prod_{i<q}\bigl((1-a)^{p^i}X+1\bigr)-1$ then has all $p$ elements of $\mathbb{F}_p$ as roots, so $p\le q$. This is Lemma C.1 of Bender--Glauberman Appendix C.
--
--   **Formalization Note** The norm set is `NormSet.normSetE p q`, its cardinality is taken with `Set.ncard`, and $E^{-1}$ is the pointwise inverse (`⁻¹` on sets).
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/AppC_NormSet.lean#L531-L608

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

theorem lemmaC1 [Fact p.Prime] (hq : q.Prime)
    (hEinv : normSetE p q = (normSetE p q)⁻¹)
    (hcard : 2 ≤ (normSetE p q).ncard) :
    p ≤ q := by sorry

end OddOrder.BG.AppC.NormSet
