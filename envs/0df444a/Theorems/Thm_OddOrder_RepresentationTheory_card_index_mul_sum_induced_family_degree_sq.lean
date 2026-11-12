-- Prove2me | Theorems.Thm_OddOrder_RepresentationTheory_card_index_mul_sum_induced_family_degree_sq
-- name    : OddOrder.RepresentationTheory.card_index_mul_sum_induced_family_degree_sq
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T05:39:01.051227+00:00
-- url     : https://prove2.me/theorems/76b29b4b-018e-4586-add2-6c46ae51065a
-- title:
--   Degree-square sum of a Frobenius induced family: $[G:H]\sum_{i\ne1}\theta_i(1)^2=|H|-1$
-- statement:
--   Let $G$ be a finite group which is a Frobenius group with kernel $H$ and complement $C$ (`Ch06.IsFrobeniusGroup G H C`; in particular $H\trianglelefteq G$), with the cardinalities of $G$ and $H$ invertible in $\mathbb{C}$. Let $n\in\mathbb{N}$ and let $\theta:\mathrm{Fin}(n+1)\to\mathrm{Irr}(H)$ be an enumeration of irreducible characters of $H$, with a distinguished index $i_1$ such that $\theta_{i_1}$ is the trivial character. Suppose that
--
--   * the induced characters $\mathrm{Ind}_H^G\theta_i$ are pairwise distinct (the map $i\mapsto\mathrm{Ind}_H^G\theta_i$ is injective), and
--   * every $\mathrm{Ind}_H^G\varphi$, for $\varphi\in\mathrm{Irr}(H)$, is of the form $\mathrm{Ind}_H^G\theta_i$ for some $i$.
--
--   Then, in $\mathbb{C}$,
--   $$[G:H]\sum_{i\ne i_1}\theta_i(1)^2=|H|-1.$$
--
--   This is Peterfalvi's $\sum a_i^2=(h-1)/e$, multiplied out: the Frobenius structure forces every fibre of $\theta\mapsto\mathrm{Ind}\,\theta$ over the nontrivial irreducible characters to have size $e=[G:H]$ with constant degree, so the Burnside sum $\sum_{\varphi\ne1}\varphi(1)^2=|H|-1$ collapses.
--
--   **Formalization Note** Characters are `IrreducibleCharacter ↥H`, regarded as class functions `ClassFunction ↥H ℂ`; induction is `induce H`; `Fintype G`, `Fintype ↥H` and the `Invertible` cardinality instances are part of the hypotheses.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/GroupTheory/RepresentationTheory/InducedDegreeSum.lean#L180-L295

import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_InducedIrreducible
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_ColumnOrthogonality

set_option linter.unusedFintypeInType false

namespace OddOrder.RepresentationTheory

open ClassFunction

variable {G : Type*} [Group G] {H : Subgroup G} [hH : H.Normal]

variable [Fintype G] [Fintype ↥H]

variable [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card ↥H : ℂ)]

section Frobenius

variable {C : Subgroup G}

theorem card_index_mul_sum_induced_family_degree_sq
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup G H C)
    {n : ℕ} (θ : Fin (n + 1) → IrreducibleCharacter ↥H) (ind1H : Fin (n + 1))
    (htriv : θ ind1H = trivialIrreducibleCharacter ↥H)
    (hinj : Function.Injective
      (fun i => induce H (θ i : ClassFunction ↥H ℂ)))
    (hcover : ∀ φ : IrreducibleCharacter ↥H,
      induce H (φ : ClassFunction ↥H ℂ) ∈
        Set.range (fun i => induce H (θ i : ClassFunction ↥H ℂ))) :
    (H.index : ℂ) * ∑ i ∈ Finset.univ.erase ind1H,
        ((θ i : ClassFunction ↥H ℂ) 1) ^ 2
      = (Nat.card ↥H : ℂ) - 1 := by sorry

end Frobenius

end OddOrder.RepresentationTheory
