-- Prove2me | Theorems.Thm_HunterPDE_Sobolev_HasWeakDeriv_zero_ae_eq
-- name    : HunterPDE.Sobolev.HasWeakDeriv.zero_ae_eq
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-14T19:24:14.505651+00:00
-- url     : https://prove2.me/theorems/92da2cfa-280d-400c-8919-d9073d2f5f9c
-- title:
--   The zeroth weak derivative equals the original function almost everywhere
-- statement:
--   Let $\Omega\subseteq\mathbb R^n$ be open. If $g$ is the weak derivative of $f$ for the zero multi-index, then $g=f$ almost everywhere in $\Omega$. The functions are locally integrable by the definition of a weak derivative. This identifies the zeroth term in the Sobolev norm with the ordinary $L^p$ norm.
-- source:
--   Hunter, Notes on Partial Differential Equations (revised 6/18/2014), https://www.math.ucdavis.edu/~hunter/pdes/ch3.pdf, p. 48, Definition 3.2 with the zero multi-index; p. 58, Definition 3.23

import Definitions.Def_HunterPDE_Sobolev_SobolevSpace

open MeasureTheory HunterPDE.Sobolev

theorem HunterPDE.Sobolev.HasWeakDeriv.zero_ae_eq {n : ℕ}
    {Ω : Set (EuclideanSpace ℝ (Fin n))} (hΩ : IsOpen Ω)
    {f g : EuclideanSpace ℝ (Fin n) → ℝ}
    (hg : HasWeakDeriv Ω (fun _ => 0) f g) :
    g =ᵐ[volume.restrict Ω] f := by sorry
