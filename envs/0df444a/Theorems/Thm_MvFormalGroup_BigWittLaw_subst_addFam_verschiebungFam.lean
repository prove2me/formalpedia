-- Prove2me | Theorems.Thm_MvFormalGroup_BigWittLaw_subst_addFam_verschiebungFam
-- name    : MvFormalGroup.BigWittLaw.subst_addFam_verschiebungFam
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.856965+00:00
-- url     : https://prove2.me/theorems/66d11d6a-3191-52cb-b13f-e48e1280c371
-- title:
--   Verschiebung commutes with the big Witt addition law
-- statement:
--   Let $R$ be a commutative ring, let $n$ be a natural number with $0 < n$, and let $k$ be a natural number. Consider the family $v \colon \mathbb{N} \to R[[X_i : i \in \mathbb{N}]]$ given by $v_j = X_{(j+1)/n-1}$ when $n \mid j+1$ and $v_j = 0$ otherwise. On one side, $v_k$ is substituted into the big Witt addition family [`MvFormalGroup.BigWittLaw.addFam R`](def/MvFormalGroup_BigWittLaw.html#L67), whose $m$-th member is the image in $R[[X_{(b,i)} : (b,i) \in \mathrm{Fin}\,2 \times \mathbb{N}]]$ of the integral polynomial $X_{(0,m)} + X_{(1,m)} + \sum_{i<m} X_{(0,i)} X_{(1,m-1-i)}$; on the other side, the $k$-th member of that same addition family has each of its variables $X_{(b,j)}$ replaced by [`MvFormalGroup.WittLaw.pairFam v (b,j)`](def/MvFormalGroup_CartierModule.html#L341), i.e. by $v_j$ with its variables transported into the $b$-th block via `WittLaw.blk b`. The assertion is that these two power series in the variables $X_{(b,i)}$ agree, for every such $R$, $n$ and $k$.
--
--   This is the statement that the $n$-th Verschiebung $a(t) \mapsto a(t^n)$, in the coordinates $a_k$ of the big Witt formal group, is an endomorphism of that formal group: applying $V_n$ to a sum computed by the big Witt addition law gives the sum of the $V_n$-images, coordinate by coordinate. It is used in the Cartier-module treatment of the big Witt law, where the Verschiebung operators enter the splitting underlying $p$-typification, through [`MvFormalGroup.CartierModule.subst_curve_eq_of_forall_map_eq_of_algebra_padicInt`](thm.html#MvFormalGroup.CartierModule.subst_curve_eq_of_forall_map_eq_of_algebra_padicInt).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvFormalGroup_BigWittLaw_subst_addFam_verschiebungFam.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_BigWittLaw

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem MvFormalGroup.BigWittLaw.subst_addFam_verschiebungFam
    (R : Type u) [CommRing R] (n : ℕ) (hn : 0 < n) (k : ℕ) :
    MvPowerSeries.subst (MvFormalGroup.BigWittLaw.addFam R)
        ((if n ∣ k + 1 then MvPowerSeries.X ((k + 1) / n - 1) else 0) : MvPowerSeries ℕ R) =
      MvPowerSeries.subst
        (MvFormalGroup.WittLaw.pairFam fun j =>
          ((if n ∣ j + 1 then MvPowerSeries.X ((j + 1) / n - 1) else 0) : MvPowerSeries ℕ R))
        (MvFormalGroup.BigWittLaw.addFam R k) := by sorry
