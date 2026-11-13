-- Prove2me | Theorems.Thm_OddOrder_Section16CharacterData_tau3W_omegaS_pair_of_coprime
-- name    : OddOrder.Section16CharacterData.tau3W_omegaS_pair_of_coprime
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T18:05:49.421879+00:00
-- url     : https://prove2.me/theorems/46c8c002-28d6-4bce-85ff-5d51283c97d7
-- title:
--   Peterfalvi (3.9.a): conjugate-pair symmetry of the $\eta$-grid on elements of order prime to $pq$
-- statement:
--   In the Section 16 setting, let $G$ be a finite group which is a minimal simple group of odd order (`hG : IsMinimalSimpleOdd G`), let `mp : Section16MaximalPair G` be a pair of maximal subgroups, and let `tp : Section16TypePStructure mp` be a type P structure on it, with primes $p=$ `tp.p` and $q=$ `tp.q`; the cardinalities of the groups $W_1$ attached to the two certain-type structures of the pair are nonzero. For $i\in\mathrm{Fin}\,q$, $j\in\mathrm{Fin}\,p$, let $\eta_{ij}=\tau_3\omega_{ij}$ be the class function `tau3W hG mp tp (omegaS hG mp tp i j)` on $G$. Let $g\in G$ be an element whose order is coprime to $pq$. Then
--   $$\eta_{-i,-j}(g)=\eta_{ij}(g),$$
--   where $(-i,-j)$ denotes the index negation $(i,j)\mapsto(-i,-j)$ on $\mathrm{Fin}\,q\times\mathrm{Fin}\,p$ (`finNeg`).
--
--   This is the conjugate-pair symmetry of Peterfalvi (3.9.a) on generic elements: the negated-index character is the inverse linear character, so $\eta_{-i,-j}(g)=\overline{\eta_{ij}(g)}$, and the value is a rational integer by (3.9.c), hence real.
--
--   **Formalization Note** The `omega`, `tau3W`, and structures `Section16MaximalPair`, `Section16TypePStructure` are project-specific encodings of the Section 16 data; `finNeg` is `OddOrder.Peterfalvi.S15.finNeg`.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/FeitThompsonCharacterData.lean#L773-L822

import Definitions.Def_OddOrder_FeitThompsonNuGrid
import Definitions.Def_OddOrder_Peterfalvi_S13_TypeDetermination
import Definitions.Def_OddOrder_FeitThompsonSetup
import Definitions.Def_OddOrder_Peterfalvi_S15_HonestTypeP2A0
import Definitions.Def_OddOrder_FeitThompsonCharacterData

namespace OddOrder

open OddOrder.BG

open OddOrder.GroupTheory

open OddOrder.Isaacs

open OddOrder.RepresentationTheory

open scoped Pointwise

universe u

section

open scoped OddOrder.Peterfalvi.S15.FiniteInduce

namespace Section16CharacterData

variable {G : Type*} [Group G] [Finite G] (hG : IsMinimalSimpleOdd G) (mp : Section16MaximalPair G)

variable (tp : Section16TypePStructure mp)

variable [NeZero (Nat.card ↥(mp.certainTypeS hG).W1)]

variable [NeZero (Nat.card ↥(mp.certainTypeT hG).W1)]

omit [NeZero (Nat.card ↥(Section16MaximalPair.certainTypeT hG mp).W1)] in
set_option backward.isDefEq.respectTransparency false in

theorem tau3W_omegaS_pair_of_coprime (i : Fin tp.q) (j : Fin tp.p) {g : G}
    (hg : Nat.Coprime (orderOf g) (tp.p * tp.q)) :
    tau3W hG mp tp (omegaS hG mp tp (OddOrder.Peterfalvi.S15.finNeg tp.q_prime.pos i)
        (OddOrder.Peterfalvi.S15.finNeg tp.p_prime.pos j)) g
      = tau3W hG mp tp (omegaS hG mp tp i j) g := by sorry

end Section16CharacterData

end

end OddOrder
