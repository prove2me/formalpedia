-- Prove2me | Theorems.Thm_MasulloRH_critical_line_mass_two_pair_certificate
-- name    : MasulloRH.critical_line_mass_two_pair_certificate
-- status  : Proved
-- author  : @meadowlark
-- created : 2026-11-21T01:23:11.509003+00:00
-- url     : https://prove2.me/theorems/25c11063-ca42-4c7f-bb46-25116e2275a3
-- title:
--   Two pairs of critical-line zeros with an explicit trace mass
-- statement:
--   There exist two disjoint pairs of zeros of the Riemann zeta function on the critical line. The absolute ordinates of the first pair lie in $(14.13,14.14)$ and those of the second pair lie in $(21.016,21.029)$. Write $m(z)$ for the order of the zero at $z$ and $K(t)=(t^2-5)/(2(t^2+25/4)(t^2+4))$. Over these four distinct zeros, the sum of $m(z)K(\Im z)$ is at least $169/25000$. For every natural $N\le 11$, the prime-side expression $\log(2)/2+\pi/4-37/30+\sum_{n<N}\Lambda(n)(n^{-5/2}-n^{-3})$ is at most $63/10000$, with the term at zero taken to be zero. The same four witnesses therefore give a margin of at least $23/50000$ for every cutoff in this range.
-- source:
--   Finite specialization of the Masullo mission’s critical-line mass comparison, https://prove2.me/theorems/bd574b97-ccdf-4e3d-aff9-98ed941abbf8. The explicit pair near 14.13 and its mass bound come from marozols’ accepted first-pair theorem, https://prove2.me/theorems/6a993fae-e7d3-461e-a029-f2eb21fc3914, using Yi’s multiplicity argument, https://prove2.me/theorems/0a35acdb-fbbc-407f-a9ce-f3f660e29b8d, and bueno_ricardo’s Lean 4.33.1 port, https://prove2.me/theorems/6f17bf2b-9b3b-46cb-9ddd-25102aba9e5b. The rational interval certificate near 21.022 adapts Thomas Lince’s Hardy Z development, https://github.com/teal-sea/zeta-lab/tree/a401821c9608526425f3d4cf7ff8e59bc37e1c79/hunts/hardy_first_zero. Hunt #133 already certified a zero in (21.02, 21.03), https://github.com/teal-sea/zeta-lab/blob/a401821c9608526425f3d4cf7ff8e59bc37e1c79/hunts/hardy_ten_zeros/RESULTS.md. The accepted comparison through 100 by marozols, https://prove2.me/theorems/a8a451bb-a157-45c1-b11e-fc5fd005e5b9, treats a larger range of cutoffs with unspecified witnesses. This statement records the cardinality, locations and joint mass of two prescribed pairs.

import Definitions.Def_MasulloRH_RegularizedTrace
import Mathlib

open MasulloRH ArithmeticFunction
open scoped Classical

theorem MasulloRH.critical_line_mass_two_pair_certificate :
    ∃ A B : Finset (ZetaZerosInTraceStrip (1/2)), A.card = 2 ∧ B.card = 2 ∧ Disjoint A B ∧
      (∀ z ∈ A, z.val.re = 1/2 ∧ 1413/100 < |z.val.im| ∧ |z.val.im| < 707/50) ∧
      (∀ z ∈ B, z.val.re = 1/2 ∧ 2627/125 < |z.val.im| ∧ |z.val.im| < 21029/1000) ∧
      169/25000 ≤ (∑ z ∈ A ∪ B, (analyticOrderNatAt riemannZeta z.val : ℝ) *
        ((z.val.im^2-5)/(2*(z.val.im^2+25/4)*(z.val.im^2+4)))) ∧
      ∀ N : ℕ, N ≤ 11 → Real.log 2/2 + Real.pi/4 - 37/30 +
        (∑ n ∈ Finset.range N, (vonMangoldt n / (n:ℝ)^(5/2:ℝ) -
          vonMangoldt n / (n:ℝ)^(3:ℝ))) ≤ 63/10000 := by sorry
