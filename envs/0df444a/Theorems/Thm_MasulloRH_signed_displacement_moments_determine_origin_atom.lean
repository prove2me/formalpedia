-- Prove2me | Theorems.Thm_MasulloRH_signed_displacement_moments_determine_origin_atom
-- name    : MasulloRH.signed_displacement_moments_determine_origin_atom
-- status  : Proved
-- author  : @Yi
-- created : 2026-11-21T14:23:08.714452+00:00
-- url     : https://prove2.me/theorems/117b2112-ccf1-46dd-adf4-81254ed7609b
-- title:
--   Weighted displacement moments characterize the residual atom at the origin
-- statement:
--   On any compact real coordinate range containing 1, if a bounded real linear functional L annihilates every (1−y)w(y)y^n, with w an invertible continuous weight, then L(f)=L(1)f(1) for every continuous f. Under y=exp(−2h), this identifies the only invisible finite signed displacement law as an atom at h=0, whose coefficient the leading Mellin term fixes.
-- source:
--   Masullo repair, translated-bump displacement family. After weighting the signed law by y^(−1/4), the tail moments have w=y^(3/2). Real polynomial density from mathlib Stone-Weierstrass.

import Mathlib
open Polynomial

theorem MasulloRH.signed_displacement_moments_determine_origin_atom (s : Set ℝ) [CompactSpace s] (a : s) (ha : (a : ℝ) = 1)
    (w : C(s, ℝ)ˣ) (L : C(s, ℝ) →L[ℝ] ℝ)
    (mom : ∀ n : ℕ, L ((1 - toContinuousMapOnAlgHom s X) * (w : C(s, ℝ)) *
      (toContinuousMapOnAlgHom s X)^n) = 0) :
    ∀ f : C(s, ℝ), L f = L 1 * f a := by sorry
