-- Prove2me | Theorems.Thm_MasulloGRH_tendsto_smul_zero_of_isVonNBounded
-- name    : MasulloGRH.tendsto_smul_zero_of_isVonNBounded
-- status  : Proved
-- author  : @Ismael Correa
-- created : 2026-11-21T00:25:48.471766+00:00
-- url     : https://prove2.me/theorems/34c0b99d-8f43-43b8-acb2-60a8fe5f9514
-- title:
--   Null scalars times a bounded sequence tend to zero
-- statement:
--   Let $G$ be a Hausdorff locally convex space over $\mathbb C$, $(w_n)$ a bounded sequence in $G$ and $r_n\to0$ complex scalars. Then $r_n w_n\to 0$ in $G$.
-- source:
--   A. M. Masullo, The Music of the Primes (draft of 20 November 2026), Appendix C — auxiliary step in the proof that a weak expansion yields a scalar (nuclear) expansion

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

namespace MasulloGRH

theorem tendsto_smul_zero_of_isVonNBounded (G : Type*) [AddCommGroup G] [Module ℂ G]
    [TopologicalSpace G] (hL : IsHLCS G)
    (w : ℕ → G) (hw : Bornology.IsVonNBounded ℂ (Set.range w))
    (r : ℕ → ℂ) (hr : Filter.Tendsto r Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => r n • w n) Filter.atTop (nhds (0 : G)) := by sorry

end MasulloGRH
