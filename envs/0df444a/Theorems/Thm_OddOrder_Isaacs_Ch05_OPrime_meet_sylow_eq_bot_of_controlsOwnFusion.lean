-- Prove2me | Theorems.Thm_OddOrder_Isaacs_Ch05_OPrime_meet_sylow_eq_bot_of_controlsOwnFusion
-- name    : OddOrder.Isaacs.Ch05.OPrime_meet_sylow_eq_bot_of_controlsOwnFusion
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T05:31:26.558462+00:00
-- url     : https://prove2.me/theorems/da911b10-d546-400a-b292-a1667a83ed1f
-- title:
--   A Sylow $p$-subgroup controlling its own fusion meets $O^p(G)$ trivially (Isaacs 5.25, converse core)
-- statement:
--   Let $G$ be a finite group, $p$ a prime, and $P$ a Sylow $p$-subgroup of $G$ that controls its own $G$-fusion (`P.ControlsOwnFusion`: elements of $P$ conjugate in $G$ are conjugate by an element of the normalizer of $P$). Then
--   $$P\cap O^p(G)=1,$$
--   where $O^p(G)$ is the intersection of all normal subgroups of $p$-power index.
--
--   This is the heart of the proof of the converse direction of Isaacs Thm 5.25. Writing $N=O^p(G)$, $P\cap N$ is a Sylow $p$-subgroup of $N$ and $A^p(N)=N$; by the focal subgroup theorem (Thm 5.21) the focal subgroup of $P\cap N$ equals $P\cap N$, and control of fusion forces it to be trivial.
--
--   **Formalization Note** $O^p(G)$ is `OPrime p G`, and `P.ControlsOwnFusion` is the predicate `Sylow.ControlsOwnFusion` on Sylow subgroups, built on `Subgroup.ControlsFusionIn`.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Isaacs/Ch05_Transfer/Main.lean#L146-L301

import Definitions.Def_OddOrder_Isaacs_Ch05_Transfer_Basic
import Definitions.Def_OddOrder_Isaacs_Ch05_Transfer_Main
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finite.Prod
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic.Group
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.GroupTheory.Nilpotent

open scoped commutatorElement

open scoped IsMulCommutative

namespace OddOrder.Isaacs.Ch05

open Pointwise

open scoped commutatorElement

variable {G : Type*} [Group G]

section

theorem OPrime_meet_sylow_eq_bot_of_controlsOwnFusion [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) (hP : P.ControlsOwnFusion) :
    (P : Subgroup G) ⊓ OPrime p G = ⊥ := by sorry

end

end OddOrder.Isaacs.Ch05
