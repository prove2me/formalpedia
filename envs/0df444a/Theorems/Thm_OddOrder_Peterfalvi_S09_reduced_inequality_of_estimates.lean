-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S09_reduced_inequality_of_estimates
-- name    : OddOrder.Peterfalvi.S09.reduced_inequality_of_estimates
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T07:34:40.491168+00:00
-- url     : https://prove2.me/theorems/d4dc50a2-94d0-4759-9ae2-c8bbf0649251
-- title:
--   Peterfalvi (7.10): reduced form of the family inequality from (7.5)
-- statement:
--   Let $G$ be a finite group and `F : FamilyHypothesis71 G k` a family of Peterfalvi (7.4) data, with subsets $A_j$, subgroups $L_j$, the set $G_0=$ `F.G0`, and the norm function `chiRhoNormSq`. Let $\chi$ be a class function on $G$ with $\langle\chi,\chi\rangle=1$, let $i<k$, let $B$ be a finite set of indices with $j\ne i$ for $j\in B$, and let $c\in\mathbb R$. Assume:
--
--   - $1\le\sum_{g\in G_0}\|\chi(g)\|^2$;
--   - $c\le\texttt{chiRhoNormSq}\,\chi\,i$;
--   - for all $j\ne i$ with $j\notin B$: $|A_j|/|L_j|\le\texttt{chiRhoNormSq}\,\chi\,j$.
--
--   Then
--   $$\frac{1-|G_0|}{|G|}+\Big(c-\frac{|A_i|}{|L_i|}-\sum_{j\in B}\frac{|A_j|}{|L_j|}\Big)\le 0 .$$
--
--   This is obtained from the basic inequality (7.5) by inserting the three estimates above, and is the real-valued input to the (7.10) character estimate.
--
--   **Formalization Note.** $G$ carries `Fintype` and `Invertible (Nat.card G : ℂ)` instances.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S09_NonexistenceCertain/Hypothesis71.lean#L1125-L1219

import Definitions.Def_OddOrder_Peterfalvi_S08_CoherenceTheorems
import Definitions.Def_OddOrder_Isaacs_Ch06_FrobeniusActions_FrobeniusGroup
import Definitions.Def_OddOrder_GroupTheory_TISubset
import Definitions.Def_OddOrder_Peterfalvi_S09_NonexistenceCertain_Hypothesis71

namespace OddOrder.Peterfalvi.S09

open OddOrder.Isaacs.Ch06 (IsFrobeniusGroup)

open OddOrder.GroupTheory (IsTISubset)

open OddOrder.RepresentationTheory

open scoped Pointwise

variable {G : Type*} [Group G]

section Section_7_4_to_7_5

open scoped Classical in

theorem reduced_inequality_of_estimates {G : Type*} [Group G] [Fintype G]
    [Invertible (Nat.card G : ℂ)] {k : ℕ}
    (F : FamilyHypothesis71 G k)
    (χ : ClassFunction G ℂ) (hχ : ClassFunction.inner χ χ = 1)
    (i : Fin k) (B : Finset (Fin k)) (c : ℝ)
    (hB_ne : ∀ j ∈ B, i ≠ j)
    (hG0 :
      (1 : ℝ) ≤
        ∑ g ∈ Finset.univ.filter (fun g : G => g ∈ F.G0),
          ‖(χ : G → ℂ) g‖ ^ 2)
    (hi : c ≤ F.chiRhoNormSq χ i)
    (hgood : ∀ j : Fin k, i ≠ j → j ∉ B →
      (Nat.card (F.A j) : ℝ) / (Nat.card (F.L j) : ℝ) ≤
        F.chiRhoNormSq χ j) :
    ((1 - (Nat.card F.G0 : ℝ)) / (Nat.card G : ℝ)) +
        (c - (Nat.card (F.A i) : ℝ) / (Nat.card (F.L i) : ℝ) -
          ∑ j ∈ B, (Nat.card (F.A j) : ℝ) / (Nat.card (F.L j) : ℝ)) ≤ 0 := by sorry

end Section_7_4_to_7_5

end OddOrder.Peterfalvi.S09
