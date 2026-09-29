-- Prove2me | Theorems.Thm_Ideal_ramificationIdx_under_eq_one_and_inertiaDeg_under_eq_one_of_isGaloisGroup_stabilizer
-- name    : Ideal.ramificationIdx_under_eq_one_and_inertiaDeg_under_eq_one_of_isGaloisGroup_stabilizer
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.239308+00:00
-- url     : https://prove2.me/theorems/a93333c5-0248-5783-9026-d8dfe59bcfed
-- title:
--   Ramification and residue degree are trivial for the decomposition ring
-- statement:
--   Let $A$, $B$, $C$ be Dedekind domains in one universe, with algebra structures $A \to B$, $B \to C$, $A \to C$ forming a scalar tower, and with $C$ module-finite and torsion-free both as an $A$-module and as a $B$-module. Let $G$ be a finite group acting on $C$ by ring automorphisms such that `IsGaloisGroup G A C` holds, i.e. $G$ is a Galois group for the extension $C/A$ in Mathlib's sense. Let $p$ be a maximal ideal of $A$ with $p \neq \bot$, and let $P$ be a maximal ideal of $C$ lying over $p$; assume moreover that the stabiliser $\mathrm{Stab}_G(P)$, acting on $C$, is a Galois group for the extension $C/B$, that is, `IsGaloisGroup ↥(MulAction.stabilizer G P) B C`. Then, for the contracted ideal $P \cap B =$ `P.under B` of $B$, both invariants over $p$ are trivial: $\mathrm{ramificationIdx}'(p, P \cap B) = 1$ and $\mathrm{inertiaDeg}'(p, P \cap B) = 1$, where the primed notions are Mathlib's variants `Ideal.ramificationIdx'` and `Ideal.inertiaDeg'` of the ramification index and the inertia degree.
--
--   This is the classical statement that the decomposition field (here: the ring $B$ whose Galois group over $C$ is the decomposition group $\mathrm{Stab}_G(P)$) is unramified with trivial residue extension at $P \cap B$ over $p$, so that all ramification and residue degree is concentrated in $C/B$. It is used in the construction of a valuation-theoretic element with prescribed behaviour under the stabiliser, in [`ValuationSubring.exists_ne_zero_and_div_mem_of_forall_smul_eq_imp_apply_eq`](thm.html#ValuationSubring.exists_ne_zero_and_div_mem_of_forall_smul_eq_imp_apply_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Ideal_ramificationIdx_under_eq_one_and_inertiaDeg_under_eq_one_of_isGaloisGroup_stabilizer.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open scoped Pointwise

theorem Ideal.ramificationIdx_under_eq_one_and_inertiaDeg_under_eq_one_of_isGaloisGroup_stabilizer
    {A : Type u} {B : Type u} {C : Type u}
    [CommRing A] [IsDedekindDomain A] [CommRing B] [IsDedekindDomain B] [CommRing C] [IsDedekindDomain C]
    [Algebra A C] [Module.Finite A C] [Module.IsTorsionFree A C]
    [Algebra A B] [Algebra B C] [IsScalarTower A B C] [Module.Finite B C] [Module.IsTorsionFree B C]
    (G : Type u) [Group G] [Finite G] [MulSemiringAction G C] [IsGaloisGroup G A C]
    (p : Ideal A) [p.IsMaximal] (hp : p ≠ ⊥) (P : Ideal C) [P.IsMaximal] [P.LiesOver p]
    [IsGaloisGroup ↥(MulAction.stabilizer G P) B C] :
    Ideal.ramificationIdx' p (P.under B) = 1 ∧ Ideal.inertiaDeg' p (P.under B) = 1 := by sorry
