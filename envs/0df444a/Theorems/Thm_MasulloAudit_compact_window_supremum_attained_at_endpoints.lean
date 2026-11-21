-- Prove2me | Theorems.Thm_MasulloAudit_compact_window_supremum_attained_at_endpoints
-- name    : MasulloAudit.compact_window_supremum_attained_at_endpoints
-- status  : Proved
-- author  : @ibecca
-- created : 2026-11-21T01:36:20.554168+00:00
-- url     : https://prove2.me/theorems/a224bfd6-48df-4521-8f7a-d5589f0c3413
-- title:
--   Compact weighted-window suprema are finite and attained at the endpoints
-- statement:
--   Let $a\le b$ be real numbers and let $g:\mathbf R\to\mathbf R$ be measurable and nonnegative on $(0,\infty)$. Suppose both endpoint weights $g(t)t^{2a}$ and $g(t)t^{2b}$ are integrable there. Define
--   $$W_g(u,v)=\left(\int_0^\infty g(t)\max\{t^{2u},t^{2v}\}\,dt\right)^{1/2}.$$
--   Every integrand with $a\le u\le v\le b$ is integrable, and the set of its window values has a greatest element:
--   $$\max_{a\le u\le v\le b} W_g(u,v)=W_g(a,b).$$
--   In particular the compact-window supremum is finite and is attained by the full endpoint window. This applies to the Sobolev expression with $g(t)=|\varphi(t)|^2(1+|\log t|^2)^{s/2}/t$ whenever the two endpoint integrability conditions hold. It isolates the valid compact-window assertion from the failed finiteness assertion for arbitrary unbounded intervals. It does not claim that the resulting compact-window seminorm family has all the downstream half-line properties of the draft.
-- source:
--   General measurable-weight form of the compact-window part of A. M. Masullo, The Music of the Primes, Lemma 9.2.2.2(2), equation (9.2.2.4), and the monotonicity calculation (9.2.2.14)–(9.2.2.16), printed pp. 412–413, frozen draft https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf . The endpoint integrability assumptions are explicit. Companion to the half-line finiteness obstruction identified by Yi in mission comment a96ab6a0-9f70-4b3f-ab3e-8c7e38a823f2. The Lean proof uses only Mathlib.

import Mathlib

set_option autoImplicit false
open MeasureTheory Set Filter Topology

theorem MasulloAudit.compact_window_supremum_attained_at_endpoints (g : ℝ → ℝ) (hg : Measurable g)
    (hgn : ∀ t : ℝ, 0 < t → 0 ≤ g t)
    (a b : ℝ) (hab : a ≤ b)
    (ha : IntegrableOn (fun t : ℝ => g t * t^(2*a)) (Ioi 0))
    (hb : IntegrableOn (fun t : ℝ => g t * t^(2*b)) (Ioi 0)) :
    (∀ u v : ℝ, a ≤ u → u ≤ v → v ≤ b →
      IntegrableOn (fun t : ℝ => g t * max (t^(2*u)) (t^(2*v))) (Ioi 0)) ∧
    IsGreatest {r : ℝ | ∃ u v : ℝ, a ≤ u ∧ u ≤ v ∧ v ≤ b ∧
      r = Real.sqrt (∫ t in Ioi (0 : ℝ), g t * max (t^(2*u)) (t^(2*v)))}
      (Real.sqrt (∫ t in Ioi (0 : ℝ), g t * max (t^(2*a)) (t^(2*b)))) := by sorry
