-- Prove2me | Theorems.Thm_ManyServerQED_Scheduling_renewal_inversion_uoc
-- name    : ManyServerQED.Scheduling.renewal_inversion_uoc
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-25T20:23:29.971808+00:00
-- url     : https://prove2.me/theorems/4e93af3d-df32-4d75-960f-3a7609f37736
-- title:
--   Uniform-on-compacts inversion of centered renewal epochs
-- statement:
--   Let $e_n(j)$ be strictly increasing renewal epochs starting at zero. Suppose the continuous limiting path $v$ is the locally uniform limit of paths $u_n$ satisfying $u_n(j/n)=(e_n(j)-j)/\sqrt n$ at every grid point. Let nonnegative $a_n$ tend to $a\geq 0$ and let $N_n$ be the inverse counting function of $e_n$. Then $[N_n(n a_n t)-n a_n t]/\sqrt n$ converges locally uniformly in $t\geq 0$ to $-v(at)$.
-- source:
--   Renewal inversion step for Atar, Mandelbaum and Reiman, Lemma 4(i), https://arxiv.org/abs/math/0407058

import Mathlib
import Definitions.Def_BellWilliams2001_ThresholdPolicy_Paths
open Filter Topology BellWilliams2001.ThresholdPolicy

theorem ManyServerQED.Scheduling.renewal_inversion_uoc
    (e : ℕ → ℕ → ℝ) (he : ∀ n, StrictMono (e n)) (he0 : ∀ n, e n 0 = 0)
    (u : ℕ → ℝ → ℝ) (v : ℝ → ℝ) (hv : Continuous v)
    (hgrid : ∀ n : ℕ, 1 ≤ n → ∀ j : ℕ,
      u n ((j:ℝ) / n) = (e n j - j) / Real.sqrt n)
    (hu : ∀ H : ℝ, 0 ≤ H → ∀ η : ℝ, 0 < η →
      ∀ᶠ n in atTop, ∀ s ∈ Set.Icc (0:ℝ) H, |u n s - v s| < η)
    (aN : ℕ → ℝ) (haN : ∀ n, 0 ≤ aN n) (a : ℝ) (ha : 0 ≤ a)
    (haLim : Tendsto aN atTop (𝓝 a)) :
    ∀ T : ℝ, 0 ≤ T → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in atTop, ∀ t ∈ Set.Icc (0:ℝ) T,
        |(((renewalCount (e n) ((n:ℝ) * aN n * t)).toNat : ℝ) -
          (n:ℝ) * aN n * t) / Real.sqrt n + v (a*t)| < ε := by sorry
