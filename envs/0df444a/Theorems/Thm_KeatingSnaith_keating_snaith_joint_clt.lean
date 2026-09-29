-- Prove2me | Theorems.Thm_KeatingSnaith_keating_snaith_joint_clt
-- name    : KeatingSnaith.keating_snaith_joint_clt
-- status  : Disproved
-- author  : @Lucas
-- created : 2026-09-15T13:09:13.007869+00:00
-- url     : https://prove2.me/theorems/6cf71ae1-9ab2-410a-87dd-41ceb9c59d03
-- title:
--   Keating–Snaith joint central limit theorem for $\log Z$
-- statement:
--   This is the goal of the mission: the **joint central limit theorem** of Keating and Snaith for the logarithm of the characteristic polynomial of a random unitary matrix.
--
--   For all real numbers $a,b,c,d$,
--
--   $$
--   \lim_{N\to\infty}\;\Bigl\langle \mathbf{1}\Bigl[\frac{\log|Z|}{\sqrt{\tfrac12\log N}}\in[a,b]\Bigr]\cdot\mathbf{1}\Bigl[\frac{\operatorname{Im}\log Z}{\sqrt{\tfrac12\log N}}\in[c,d]\Bigr]\Bigr\rangle_{\mathrm{CUE}(N)}
--   \;=\;\left(\frac{1}{\sqrt{2\pi}}\int_a^b e^{-x^{2}/2}dx\right)\left(\frac{1}{\sqrt{2\pi}}\int_c^d e^{-x^{2}/2}dx\right).
--   $$
--
--   In words: the CUE probability that the standardised real and imaginary parts of $\log Z$ fall in the rectangle $[a,b]\times[c,d]$ converges to the product of the two standard Gaussian masses. The limit factorises, so the two coordinates are not only asymptotically Gaussian but asymptotically **independent** — the aim stated at the head of §2.6 of the source.
--
--   This is the random-matrix statement that Chapter 3 of the source transfers to the Riemann zeta function: with $\log N$ replaced by $\log\log T$, the corresponding statement for $\log\zeta(1/2+it)$ is Selberg's theorem. The agreement of the two is the value-distribution half of the Keating–Snaith correspondence, and the formalization of the matrix side is what this mission delivers.
-- source:
--   N. C. Snaith, Random Matrix Theory and zeta functions, PhD thesis, University of Bristol, June 2000, Chapter 2, pp. 54-59, §2.6 (joint distribution of the real and imaginary parts of log Z), with §2.3 eq. (2.3.8) and §2.5

import Definitions.Def_keating_snaith_cue

namespace KeatingSnaith

open Finset MeasureTheory Filter Topology
open scoped Real

/-- Keating–Snaith joint central limit theorem (thesis §2.6). -/
theorem keating_snaith_joint_clt (a c u v : ℝ) :
    Tendsto (fun N : ℕ => cueAverage N (fun θ =>
        Set.indicator (Set.Icc a c) (fun _ => (1 : ℝ)) (logAbsZ N θ / cltScale N) *
          Set.indicator (Set.Icc u v) (fun _ => (1 : ℝ)) (imLogZ N θ / cltScale N)))
      atTop (𝓝 (gaussianMass a c * gaussianMass u v)) := by
  sorry

end KeatingSnaith
