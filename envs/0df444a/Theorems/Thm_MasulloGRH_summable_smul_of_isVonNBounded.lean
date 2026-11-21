-- Prove2me | Theorems.Thm_MasulloGRH_summable_smul_of_isVonNBounded
-- name    : MasulloGRH.summable_smul_of_isVonNBounded
-- status  : Proved
-- author  : @Ismael Correa
-- created : 2026-11-21T00:25:47.287554+00:00
-- url     : https://prove2.me/theorems/4f476767-4023-42c4-836f-591de5b87aaa
-- title:
--   Absolutely summable combinations of a bounded sequence converge in a complete LCS
-- statement:
--   Let $G$ be a complete Hausdorff locally convex space over $\mathbb C$, $(w_n)$ a bounded sequence in $G$ and $(d_n)$ complex scalars with $\sum_n|d_n|<\infty$. Then the series $\sum_n d_n w_n$ is (unconditionally) summable in $G$.
--
--   Indeed for every continuous seminorm $p$, $\sum_n |d_n|\,p(w_n)\le \sup_n p(w_n)\sum_n|d_n|<\infty$, so the finite partial sums form a Cauchy net, which converges by completeness.
-- source:
--   A. M. Masullo, The Music of the Primes (draft of 20 November 2026), Appendix C — auxiliary step in the proof that a weak expansion yields a scalar (nuclear) expansion

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

namespace MasulloGRH

theorem summable_smul_of_isVonNBounded (G : Type*) [AddCommGroup G] [Module ℂ G]
    [TopologicalSpace G] (hC : IsCompleteTVS G) (hL : IsHLCS G)
    (w : ℕ → G) (hw : Bornology.IsVonNBounded ℂ (Set.range w))
    (d : ℕ → ℂ) (hd : Summable (fun n => ‖d n‖)) :
    Summable (fun n => d n • w n) := by sorry

end MasulloGRH
