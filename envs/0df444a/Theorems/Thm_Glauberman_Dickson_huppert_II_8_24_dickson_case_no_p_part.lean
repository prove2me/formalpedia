-- Prove2me | Theorems.Thm_Glauberman_Dickson_huppert_II_8_24_dickson_case_no_p_part
-- name    : Glauberman.Dickson.huppert_II_8_24_dickson_case_no_p_part
-- status  : Proved
-- author  : @arexychen
-- created : 2026-09-12T10:29:55.462378+00:00
-- url     : https://prove2.me/theorems/d8e36c16-39d7-4089-acc0-580aa39d3105
-- title:
--   Dickson classification for subgroups of PSL₂ of order prime to the characteristic
-- statement:
--   Let $F$ be a finite field with $|F|=p^f$, where $p$ is prime, and let $H\le\mathrm{PSL}_2(F)$ have order not divisible by $p$. Put $d=\gcd(|F|-1,2)$. Then $H$ is cyclic of order $z$ or dihedral of order $2z$, where $z$ divides $(|F|-1)/d$ or $(|F|+1)/d$, or it is isomorphic to one of $A_4,S_4,A_5$.
--   $$p\nmid|H|\quad\Longrightarrow\quad H\text{ belongs to these five families}. $$
--   The exceptional alternatives carry the classical numerical restrictions: $p\ne2$ or $f$ even for $A_4$; $16\mid p^{2f}-1$ for $S_4$; and $p=5$ or $5\mid p^{2f}-1$ for $A_5$. This is Huppert II.8.24, the characteristic-coprime part of Dickson subgroup classification.
-- source:
--   Original formalization by Qiuzhen-CFSG/CFSG and its source authors, Apache-2.0, commit 96b2a02085dc678f3e0a97b334c31ada599c55fd. Exact source: https://github.com/Qiuzhen-CFSG/CFSG/blob/96b2a02085dc678f3e0a97b334c31ada599c55fd/Glauberman/DicksonClassification.lean . Classical result: Huppert II.8.24 / Dickson. This publication replays the original proof and required source closure in Lean v4.33.1 / Mathlib 0df444a, preserving attribution and license. arexychen contributes packaging, namespace isolation and validation, not authorship of the classification proof or mathematical result.

import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.GroupTheory.SpecificGroups.Dihedral
set_option autoImplicit false
universe u

namespace Glauberman.Dickson
theorem huppert_II_8_24_dickson_case_no_p_part
    {F : Type u} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime]
    (hFcard : Nat.card F = p ^ f) (H : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F))
    (hp_not_dvd_card_H : ¬ p ∣ Nat.card H) :
    (∃ z : ℕ,
      ((z ∣ (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2) ∨
        (z ∣ (Nat.card F + 1) / Nat.gcd (Nat.card F - 1) 2)) ∧
      Nat.card H = z ∧ IsCyclic H) ∨
    (∃ z : ℕ,
      ((z ∣ (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2) ∨
        (z ∣ (Nat.card F + 1) / Nat.gcd (Nat.card F - 1) 2)) ∧
      Nat.card H = 2 * z ∧ Nonempty (H ≃* DihedralGroup z)) ∨
    ((p ≠ 2 ∨ Even f) ∧ Nonempty (H ≃* alternatingGroup (Fin 4))) ∨
    ((16 ∣ p ^ (2 * f) - 1) ∧ Nonempty (H ≃* Equiv.Perm (Fin 4))) ∨
    ((p = 5 ∨ 5 ∣ p ^ (2 * f) - 1) ∧
      Nonempty (H ≃* alternatingGroup (Fin 5))) := by sorry
end Glauberman.Dickson
