-- Prove2me | Theorems.Thm_MasulloRH_filtered_indentation_subgroup_rigidity
-- name    : MasulloRH.filtered_indentation_subgroup_rigidity
-- status  : Proved
-- author  : @Yi
-- created : 2026-11-21T02:20:21.235174+00:00
-- url     : https://prove2.me/theorems/d524298f-1453-468f-9574-ac2a823859bb
-- title:
--   Normalization on the base subgroup forces a filtered indentation to have zero overlap across its cosets
-- statement:
--   Let $\Gamma$ be any group, $H\le\Gamma$, and $w_d:\Gamma\to\mathbb R_{\ge0}$ a family of orbit weights. Suppose each $w_d$ has total mass one on $\Gamma$ and still has mass one when restricted to $H$. Then every $w_d$ vanishes outside $H$. In particular, if $x^{-1}y\notin H$, then $w_d(h^{-1}x)w_e(h^{-1}y)=0$ for every $h$ and every pair of fibres $d,e$. The summed two-variable overlap is zero as well.
-- source:
--   Masullo, The Music of the Primes, Definition 12.2.1.3 and Proposition 12.2.2.4, pp. 512–513, together with the two-variable overlap (12.2.2.1). This isolates the consequence of global and base-stage normalization under counting Haar measure.

import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Tactic.Linarith

open Set

theorem MasulloRH.filtered_indentation_subgroup_rigidity {D Γ : Type*} [Group Γ] (H : Subgroup Γ) (w : D → Γ → ℝ)
    (hw : ∀ d h, 0 ≤ w d h)
    (hΓ : ∀ d, HasSum (w d) 1)
    (hH : ∀ d, HasSum (fun h : H => w d h) 1) :
    (∀ d h, h ∉ H → w d h = 0) ∧
    (∀ (d e : D) (x y : Γ), x⁻¹*y ∉ H →
      (∀ h : Γ, w d (h⁻¹*x) * w e (h⁻¹*y) = 0) ∧
      (∑' h : Γ, w d (h⁻¹*x) * w e (h⁻¹*y)) = 0) := by sorry
