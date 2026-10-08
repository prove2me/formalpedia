-- Prove2me | Theorems.Thm_Kesten_isAmenableAction_iff_limsup_stepProb_rpow_eq_one
-- name    : Kesten.isAmenableAction_iff_limsup_stepProb_rpow_eq_one
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-07T09:25:01.275292+00:00
-- url     : https://prove2.me/theorems/3cbd1bff-ad90-433e-981f-07d34196eb0d
-- title:
--   Kesten's criterion (external) — a transitive action is amenable exactly when the return probabilities have exponential rate 1
-- statement:
--   Let a finitely generated group $H$ act transitively on a set $Y$, and let $\nu$ be a finitely supported, symmetric probability measure on $H$ whose support generates $H$. Let $p_n(y_0, y_0)$ be the probability that the random walk on $Y$ started at $y_0$, which moves from $y$ to $h y$ with probability $\nu(h)$, is back at $y_0$ after $n$ steps. Then the action of $H$ on $Y$ is amenable (there is an $H$-invariant mean on $Y$) if and only if
--
--   $$\limsup_{n\to\infty} p_n(y_0, y_0)^{1/n} = 1.$$
--
--   Juschenko, Matte Bon, Monod and de la Salle, p. 15: “By Kesten’s amenability criterion for a graph (see [Woe00, Theorem 10.6]), amenability of the action $(\mathbf Z/2\mathbf Z)^{(X)} \rtimes G \curvearrowright (\mathbf Z/2\mathbf Z)^{(X)}$ is thereby equivalent to $\lim_{n\to\infty} -\frac{1}{n} \log \mathbb P(f_n = f_0) = 0$.”
--
--   *Formalization note.* The paper applies the criterion to one walk, a lazy one, for which the return probabilities are positive and the limit exists. Stated for every symmetric generating $\nu$, the limit can fail to exist, since the return probabilities can vanish at every odd time (`IntervalExchange.exists_isSymmetric_isNondegenerate_and_stepProb_eq_zero_of_odd`), so the statement takes the $\limsup$, the spectral radius of Woess's formulation.
-- source:
--   Juschenko, K., Matte Bon, N., Monod, N. and de la Salle, M., Extensive amenability and an application to interval exchanges, Ergodic Theory Dynam. Systems 38 (2018) 195–219, https://doi.org/10.1017/etds.2016.32 (arXiv:1503.04977v1, whose page numbers are used), p. 15, Kesten's amenability criterion for a graph, which cites Woess, W., Random Walks on Infinite Graphs and Groups, Cambridge University Press, 2000, https://doi.org/10.1017/CBO9780511470967, Theorem 10.6

import Mathlib
import Definitions.Def_IntervalExchange

open IntervalExchange

namespace Kesten

theorem isAmenableAction_iff_limsup_stepProb_rpow_eq_one {H Y : Type*} [Group H] [MulAction H Y]
    [Group.FG H] [MulAction.IsPretransitive H Y] (ν : H →₀ ℝ)
    (hν : ThompsonAmenability.IsProbability ν) (hsymm : IsSymmetric ν) (hnd : IsNondegenerate ν)
    (y₀ : Y) :
    IsAmenableAction H Y ↔
      Filter.limsup (fun n : ℕ => stepProb (walkKernel (ν : H → ℝ)) n y₀ y₀ ^ (1 / (n : ℝ)))
        Filter.atTop = 1 := by
  sorry

end Kesten
