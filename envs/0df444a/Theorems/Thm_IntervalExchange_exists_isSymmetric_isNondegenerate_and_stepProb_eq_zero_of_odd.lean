-- Prove2me | Theorems.Thm_IntervalExchange_exists_isSymmetric_isNondegenerate_and_stepProb_eq_zero_of_odd
-- name    : IntervalExchange.exists_isSymmetric_isNondegenerate_and_stepProb_eq_zero_of_odd
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-07T09:25:15.646529+00:00
-- url     : https://prove2.me/theorems/1f255f32-e9bb-456b-bd14-77b5478327d1
-- title:
--   A symmetric random walk with generating support can have zero return probability at every odd time
-- statement:
--   On the group $\mathbf Z/2\mathbf Z$, written multiplicatively and acting on itself, there is a finitely supported, symmetric probability measure $\nu$ whose support generates the group, such that the random walk induced by $\nu$, started at the identity, is at the identity with probability $0$ after every odd number of steps.
--
--   Juschenko, Matte Bon, Monod and de la Salle, p. 15: “By Kesten’s amenability criterion for a graph (see [Woe00, Theorem 10.6]), amenability of the action $(\mathbf Z/2\mathbf Z)^{(X)} \rtimes G \curvearrowright (\mathbf Z/2\mathbf Z)^{(X)}$ is thereby equivalent to $\lim_{n\to\infty} -\frac{1}{n} \log \mathbb P(f_n = f_0) = 0$.”
--
--   Stated for every symmetric generating measure, the limit of $-\frac1n \log p_n$ need not exist: here $p_n = 0$ for every odd $n$, so $\log p_n$ is undefined at every odd time. The IET mission's statement of Kesten's criterion (`Kesten.isAmenableAction_iff_limsup_stepProb_rpow_eq_one`) therefore uses $\limsup_n p_n^{1/n}$.
-- source:
--   Juschenko, K., Matte Bon, N., Monod, N. and de la Salle, M., Extensive amenability and an application to interval exchanges, Ergodic Theory Dynam. Systems 38 (2018) 195–219, https://doi.org/10.1017/etds.2016.32 (arXiv:1503.04977v1, whose page numbers are used), p. 15, the use of Kesten's criterion (printed-fails lemma, not in the paper)

import Mathlib
import Definitions.Def_IntervalExchange

namespace IntervalExchange

theorem exists_isSymmetric_isNondegenerate_and_stepProb_eq_zero_of_odd :
    ∃ ν : Multiplicative (ZMod 2) →₀ ℝ, ThompsonAmenability.IsProbability ν ∧ IsSymmetric ν ∧
      IsNondegenerate ν ∧
      ∀ n : ℕ, Odd n → stepProb (walkKernel (ν : Multiplicative (ZMod 2) → ℝ)) n (1 : Multiplicative (ZMod 2)) 1 = 0 := by
  sorry

end IntervalExchange
