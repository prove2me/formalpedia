-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S15_CharacterDegreeCore_exists_caseB_data_eta10_H_core
-- name    : OddOrder.Peterfalvi.S15.CharacterDegreeCore.exists_caseB_data_eta10_H_core
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T17:02:29.1832+00:00
-- url     : https://prove2.me/theorems/70988fc2-8931-4fab-9730-7a7f0db56ecb
-- title:
--   Peterfalvi (13.5)/(13.7): integral Parseval data and inflation bound for $\eta_{10}$ on $H^\#$ (Core form)
-- statement:
--   Let $G$ be a minimal simple group of odd order (`IsMinimalSimpleOdd G`), and let `hyp : Hypothesis` be the Peterfalvi (13.1) configuration for $G$: two maximal subgroups $S,T$ with $W=S\cap T=W_1W_2$ cyclic, $|W_1|=q$, $|W_2|=p$ ($p,q$ odd primes), $P=S_F$ and $Q=T_F$ the maximal nilpotent normal Hall subgroups, complements $U,V$ with $S'=PU$, $T'=QV$, $C=C_U(P)$, $D=C_V(Q)$, $|U|=uc$, $|V|=vd$, together with the associated character grids $\eta_{ij}$, $\mu_{ij}$, $\nu_{ij}$ ($i<q$, $j<p$). Here $H=PC\le S$, $H^\#=H\setminus\{1\}$ and $\eta_{10}$ denotes `hyp.eta10`. Let `core : CharacterDegreeCore hyp` be the Core character-degree data attached to `hyp`. Then there exist a function $\alpha:G\to\mathbb C$ and natural numbers $d,n,s$ such that
--
--   $$\eta_{10}(x)=\alpha(x)\ (x\in H^\#),\quad \sum_{x\in H^\#}|\alpha(x)|^2=s,\quad n\ge 1,\quad s+d^2=|H|\,n,\quad (p^q-1)\,d^2\le s,\quad (n=1\Rightarrow d^2=1).$$
--
--   This packages the (13.5)/(13.7) correction of $\eta_{10}$ on $H^\#$ (Parseval identity, inflation bound and the abelian equality case) in the Case B endgame of Peterfalvi Section 13.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S15_CaseBEndgameSupply/Eta10HCorrection.lean#L84-L256

import Definitions.Def_OddOrder_Peterfalvi_S15_CharacterDegreeEnginesSSide
import Definitions.Def_OddOrder_Peterfalvi_S15_CharacterDegreeEngines
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_Canonicalization

namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

variable {G : Type*} [Group G]

section

open scoped Classical in
open scoped FiniteInduce in

theorem CharacterDegreeCore.exists_caseB_data_eta10_H_core [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {hyp : Hypothesis (G := G)}
    (core : CharacterDegreeCore hyp) :
    ∃ (α : G → ℂ) (d n s : ℕ),
      (∀ x ∈ (Set.toFinite (sharpSubgroup hyp.H)).toFinset, hyp.eta10 x = α x) ∧
      (∑ x ∈ (Set.toFinite (sharpSubgroup hyp.H)).toFinset, ‖α x‖ ^ 2 = (s : ℝ)) ∧
      1 ≤ n ∧ s + d ^ 2 = Nat.card ↥hyp.H * n ∧
      (hyp.p ^ hyp.q - 1) * d ^ 2 ≤ s ∧ (n = 1 → d ^ 2 = 1) := by sorry

end

end OddOrder.Peterfalvi.S15
