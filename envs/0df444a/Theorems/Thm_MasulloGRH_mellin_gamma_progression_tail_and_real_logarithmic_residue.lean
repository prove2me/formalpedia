-- Prove2me | Theorems.Thm_MasulloGRH_mellin_gamma_progression_tail_and_real_logarithmic_residue
-- name    : MasulloGRH.mellin_gamma_progression_tail_and_real_logarithmic_residue
-- status  : Proved
-- author  : @Yi
-- created : 2026-11-21T04:46:08.877604+00:00
-- url     : https://prove2.me/theorems/51c826c9-f06e-4097-b439-3236b3af590a
-- title:
--   Geometric tails for supported Mellin samples and the sign of the real gamma logarithmic residue
-- statement:
--   Let a measurable complex function $f$ on the positive ray vanish almost everywhere on $0<x<A$, where $A>1$. Fix $b$ with $M_b=\int_0^\infty x^{b-1}|f(x)|\,dx<\infty$. Its actual Mellin integral $\Phi(s)$ converges on $\Re s\le b$, where $|\Phi(s)|\le M_bA^{\Re(s)-b}$. For any $d>0$ and any complex samples $z_n$ with $\Re z_n\le b-dn$, the series of $|\Phi(z_n)|$ converges and its tail starting at $N$ is bounded by $M_b A^{-dN}/(1-A^{-d})$. The bound is uniform over all choices of imaginary parts. If $b>0$, then $s\Phi(s)(\Gamma_{\mathbf R}'/\Gamma_{\mathbf R})(s)\to -\Phi(0)$ as $s\to0$, $s\ne0$, for the actual real-place factor $\Gamma_{\mathbf R}(s)=\pi^{-s/2}\Gamma(s/2)$. These give, respectively, the absolute convergence needed for the archimedean matrix-trace series in 7.4.3.2(2) and the logarithmic residue sign at its trivial real-place pole.
-- source:
--   Masullo, The Music of the Primes, frozen draft 20 November 2026, Theorem 7.4.3.2(2), printed pp.372–374, equations (7.4.3.14) and (7.4.3.15), together with (B.1.1.7–8). Uses Mathlib's Mellin transform, Deligne's real gamma factor, and the known simple-pole residue of that factor.

import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open MeasureTheory Set Filter
open scoped Topology

theorem MasulloGRH.mellin_gamma_progression_tail_and_real_logarithmic_residue (f : ℝ → ℂ) (A b : ℝ) (hA : 1 < A)
    (hm : AEStronglyMeasurable f (volume.restrict (Ioi 0)))
    (hsupp : ∀ᵐ x ∂volume.restrict (Ioi 0), x < A → f x = 0)
    (hint : IntegrableOn (fun x : ℝ => x^(b-1) * ‖f x‖) (Ioi 0)) :
    let M := ∫ x : ℝ in Ioi 0, x^(b-1) * ‖f x‖
    (0 < b → Tendsto (fun z : ℂ => z * (mellin f z * logDeriv Complex.Gammaℝ z))
      (𝓝[≠] 0) (𝓝 (-mellin f 0))) ∧
    (∀ s : ℂ, s.re ≤ b → MellinConvergent f s ∧ ‖mellin f s‖ ≤ A^(s.re-b) * M) ∧
      ∀ (d : ℝ), 0 < d → ∀ z : ℕ → ℂ, (∀ n : ℕ, (z n).re ≤ b-d*n) →
        Summable (fun n => ‖mellin f (z n)‖) ∧
          ∀ N : ℕ, (∑' n : ℕ, ‖mellin f (z (N+n))‖) ≤
            M * (A^(-d))^N / (1-A^(-d)) := by sorry
