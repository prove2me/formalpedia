-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S16_bessel_bound_of_inner_beta_zeta_ne_zero
-- name    : OddOrder.Peterfalvi.S16.bessel_bound_of_inner_beta_zeta_ne_zero
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T15:25:30.605233+00:00
-- url     : https://prove2.me/theorems/3b13d83c-9199-46ba-98f6-753b4ee5e2de
-- title:
--   Peterfalvi (14.14): single-branch Bessel bound $(h_L-1)/e_L\le e_M-1$
-- statement:
--   Let $G$ be a finite group which is minimal simple odd-order (`hG`), and let $L,M$ be maximal subgroups of $G$ that are not conjugate (`¬ IsConjugateSubgroup L M`), with (7.8) coherence data `dataL : TypeICoherent78Data L` and `dataM : TypeICoherent78Data M`. Let $\beta_M=$ `(dataM.h78 hG).beta` and let $\nu(\zeta_*)$ be the coherent image `(dataL.h78 hG).nu ((dataL.h78 hG).hyp76.zeta (dataL.h78 hG).zetaDistinct)` of the distinguished member of the $L$-family. Assume
--   $$\langle\beta_M,\ \nu(\zeta_*)\rangle\neq0 .$$
--   Then, in $\mathbb{Q}$,
--   $$\frac{h_L-1}{e_L}\;\le\;e_M-1,$$
--   where $h_L=|\texttt{dataL.kernelIn}|$ (`Nat.card`), $e_L=[L:\texttt{dataL.kernelIn}]$ is the index of `dataL.kernelIn` and $e_M$ is the complement index `(dataM.h78 hG).complementIndex`.
--
--   The proof compares the Bessel inequality for the $L$-family with $\|\Gamma_M\|^2\le e_M-1$ ((7.8.b)), using the degree-square sum $\sum d_i^2=(h_L-1)/e_L$.
--
--   **Formalization Note.** The theorem is stated in a section with variables `[Finite G]`, `L M`, `dataL`, `dataM`, `hG`; subtractions $h_L-1$ and $e_M-1$ are performed after casting to $\mathbb{Q}$.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S16_PairingBessel.lean#L418-L531

import Definitions.Def_OddOrder_Peterfalvi_S16_PairingCoherence
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_InducedIrreducible
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_ColumnOrthogonality

namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Peterfalvi.S09

open OddOrder.Peterfalvi.S09.Cert

open scoped OddOrder.Peterfalvi.S12.FiniteInduce

variable {G : Type*} [Group G]

section Pairing

variable [Finite G] {L M : Subgroup G}

variable (dataL : TypeICoherent78Data L) (dataM : TypeICoherent78Data M)

variable (hG : OddOrder.BG.IsMinimalSimpleOdd G)

theorem bessel_bound_of_inner_beta_zeta_ne_zero
    (hL : L ∈ maximalSubgroups G) (hM : M ∈ maximalSubgroups G)
    (hnc : ¬ OddOrder.BG.Ch4.S14.IsConjugateSubgroup L M)
    (hpair : ClassFunction.inner ((dataM.h78 hG).beta)
        ((dataL.h78 hG).nu
          ((dataL.h78 hG).hyp76.zeta ((dataL.h78 hG).zetaDistinct))) ≠ 0) :
    ((Nat.card ↥dataL.kernelIn : ℚ) - 1) / (((dataL.kernelIn).index : ℕ) : ℚ)
      ≤ (((dataM.h78 hG).complementIndex : ℕ) : ℚ) - 1 := by sorry

end Pairing

end OddOrder.Peterfalvi.S16
