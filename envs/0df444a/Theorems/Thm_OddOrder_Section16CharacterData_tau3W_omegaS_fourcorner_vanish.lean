-- Prove2me | Theorems.Thm_OddOrder_Section16CharacterData_tau3W_omegaS_fourcorner_vanish
-- name    : OddOrder.Section16CharacterData.tau3W_omegaS_fourcorner_vanish
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T18:03:59.253165+00:00
-- url     : https://prove2.me/theorems/7ac89217-9dc8-40c2-9525-ab618f0f19d0
-- title:
--   Peterfalvi (3.4)/(3.5): four-corner vanishing of the $\eta$-grid off the saturation of $V$
-- statement:
--   In the Section 16 setting, let $G$ be a finite group which is a minimal simple group of odd order (`hG : IsMinimalSimpleOdd G`), let `mp : Section16MaximalPair G` be a pair of maximal subgroups and `tp : Section16TypePStructure mp` a type P structure with primes $p=$ `tp.p`, $q=$ `tp.q` (the relevant $W_1$ groups having nonzero order). For $i\in\mathrm{Fin}\,q$, $j\in\mathrm{Fin}\,p$ write $\eta_{ij}=$ `tau3W hG mp tp (omegaS hG mp tp i j)` for the associated class function on $G$. Let $i\ne0$ and $j\ne0$ (nonzero row and column indices), and let $x\in G$ lie outside the conjugacy saturation of the regular set $V$ (`(tiCyclicW hG mp tp).V`), i.e. $x\notin\bigcup_{g}gVg^{-1}$. Then
--   $$1-\eta_{i0}(x)-\eta_{0j}(x)+\eta_{ij}(x)=0.$$
--
--   This is the relation $\tau(\alpha_{AB})=1_G-\chi_{A1}-\chi_{1B}+\chi_{AB}$ of Peterfalvi (3.5), evaluated where the $V$-supported $\tau(\alpha)$ vanishes.
--
--   **Formalization Note** The sets and characters (`omegaS`, `tau3W`, `tiCyclicW`) are project-specific encodings of the Section 16 data; `Group.conjugatesOfSet` denotes the union of conjugates.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/FeitThompsonCharacterData.lean#L982-L1063

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

theorem tau3W_omegaS_fourcorner_vanish (i : Fin tp.q) (j : Fin tp.p)
    (hi : i ≠ ⟨0, tp.q_prime.pos⟩) (hj : j ≠ ⟨0, tp.p_prime.pos⟩) {x : G}
    (hx : x ∉ Group.conjugatesOfSet ((tiCyclicW hG mp tp).V)) :
    (1 : ℂ) - tau3W hG mp tp (omegaS hG mp tp i ⟨0, tp.p_prime.pos⟩) x
      - tau3W hG mp tp (omegaS hG mp tp ⟨0, tp.q_prime.pos⟩ j) x
      + tau3W hG mp tp (omegaS hG mp tp i j) x = 0 := by sorry

end Section16CharacterData

end

end OddOrder
