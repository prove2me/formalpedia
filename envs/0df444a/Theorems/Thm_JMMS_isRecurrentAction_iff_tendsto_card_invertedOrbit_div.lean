-- Prove2me | Theorems.Thm_JMMS_isRecurrentAction_iff_tendsto_card_invertedOrbit_div
-- name    : JMMS.isRecurrentAction_iff_tendsto_card_invertedOrbit_div
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-07T09:26:11.78999+00:00
-- url     : https://prove2.me/theorems/c6b95adf-8d14-4050-bfeb-7429e9c3eb2e
-- title:
--   Lemma 4.3 — a transitive action of a finitely generated group is recurrent exactly when E|O_n|/n → 0
-- statement:
--   Let a finitely generated group $G$ act transitively on a set $X$, let $\mu$ be a finitely supported, symmetric probability measure on $G$ whose support generates $G$, and let $x_0 \in X$. For the left random walk $g_n = h_n \cdots h_1$ with independent steps $h_i$ of law $\mu$, let $O_n = \{x_0, g_1^{-1} x_0, \dots, g_n^{-1} x_0\}$ be the inverted orbit. Then the action is recurrent if and only if $\frac1n \mathbb E|O_n| \to 0$.
--
--   Juschenko, Matte Bon, Monod and de la Salle, p. 16: “Lemma 4.3 ([BE11],[AV12]). Assume that $G$ is finitely generated and the action $G \curvearrowright X$ is transitive. Then $G \curvearrowright X$ is recurrent if and only if $\frac{1}{n}\mathbb E|\mathbf O_n| \to 0$ for some (equivalently for any) non-degenerate symmetric, finitely supported probability measure $\mu$ on $G$.” The inverted orbit is defined on p. 14, (1).
--
--   The statement holds for every such $\mu$, which gives both “for some” and “for any”.
-- source:
--   Juschenko, K., Matte Bon, N., Monod, N. and de la Salle, M., Extensive amenability and an application to interval exchanges, Ergodic Theory Dynam. Systems 38 (2018) 195–219, https://doi.org/10.1017/etds.2016.32 (arXiv:1503.04977v1, whose page numbers are used), p. 16, Lemma 4.3 (Bartholdi–Erschler)

import Mathlib
import Definitions.Def_IntervalExchange

open IntervalExchange

namespace JMMS

theorem isRecurrentAction_iff_tendsto_card_invertedOrbit_div {G X : Type*} [Group G]
    [MulAction G X] [DecidableEq X] [Group.FG G] [MulAction.IsPretransitive G X] (μ : G →₀ ℝ)
    (hμ : ThompsonAmenability.IsProbability μ) (hsymm : IsSymmetric μ) (hnd : IsNondegenerate μ)
    (x₀ : X) :
    IsRecurrentAction G X ↔
      Filter.Tendsto
        (fun n : ℕ => (1 / (n : ℝ)) * walkExp μ n fun h => ((invertedOrbit x₀ h).card : ℝ))
        Filter.atTop (nhds 0) := by
  sorry

end JMMS
