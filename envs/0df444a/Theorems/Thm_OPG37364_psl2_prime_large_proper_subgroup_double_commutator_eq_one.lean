-- Prove2me | Theorems.Thm_OPG37364_psl2_prime_large_proper_subgroup_double_commutator_eq_one
-- name    : OPG37364.psl2_prime_large_proper_subgroup_double_commutator_eq_one
-- status  : Proved
-- author  : @arexychen
-- created : 2026-09-12T09:42:30.492987+00:00
-- url     : https://prove2.me/theorems/ebfb4b2b-e03f-4732-aa5a-2e587a69b92e
-- title:
--   Large proper subgroups of PSL₂ over a prime field satisfy the metabelian law
-- statement:
--   Let $q\ge5$ be a prime and let $H$ be a proper subgroup of $\mathrm{PSL}_2(\mathbb F_q)$ with more than $60$ elements. Then for every $a,b,c,d\in H$,
--   $$[[a,b],[c,d]]=1,$$
--   where $[x,y]=xyx^{-1}y^{-1}$. Thus the theorem states the metabelian law directly. It does not require $H$ to be normal and does not assume a classification theorem as a hypothesis.
-- source:
--   Classical mathematics: Dickson, Huppert II.8.27, and the weak prime-field consequence in Davidoff–Sarnak–Valette §3.3. Original classification formalization: Qiuzhen-CFSG/CFSG and its source authors, Apache-2.0, immutable commit 96b2a02085dc678f3e0a97b334c31ada599c55fd: https://github.com/Qiuzhen-CFSG/CFSG/blob/96b2a02085dc678f3e0a97b334c31ada599c55fd/Glauberman/DicksonClassification.lean . The complete proof upload retains the required 19-module source closure and license. arexychen contributes the target-environment replay, prime-field specialization, integration and validation, not original authorship of the classification or classical result. Only import/visibility/scope packaging changes are made to upstream sources.

import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Commutator.Basic
set_option autoImplicit false
open scoped commutatorElement

namespace OPG37364
theorem psl2_prime_large_proper_subgroup_double_commutator_eq_one
    (q : ℕ) [Fact q.Prime] (_hq5 : 5 ≤ q)
    (H : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod q)))
    (hproper : H ≠ ⊤) (hcard : 60 < Nat.card H) (a b c d : H) :
    ⁅⁅a, b⁆, ⁅c, d⁆⁆ = 1 := by sorry
end OPG37364
