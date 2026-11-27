-- Prove2me | Theorems.Thm_MetricTSPSublinear_net_size_bound
-- name    : MetricTSPSublinear.net_size_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-27T04:15:41.976335+00:00
-- url     : https://prove2.me/theorems/a1364d0a-1caf-43d9-a879-80a1c6bfc8df
-- title:
--   Size bound for $r$-nets: $|R|\,\tau\le 2M$
-- statement:
--   Let $d$ be a metric on $V=\{0,\dots,n-1\}$ with minimum spanning tree weight $M$. If $R\subseteq V$ has at least two points and every two distinct points of $R$ are at distance at least $\tau\ge 0$, then
--   $$|R|\,\tau\le 2M .$$
--   In particular an $r$-net $N$ (a set of points with pairwise distances greater than $r$ that is within distance $r$ of every point) has $|N|\le \max(1, 2M/r)$.
--
--   The paper uses this bound to control the number of row queries spent on each $r$-net in the core refinement: for $r=\widehat M\,n^{-1+a/10}$ it gives $|N|=O(n^{1-a/10})$.
--
--   **Formalization Note** The constant $2$ comes from $\mathrm{TSP}\le M+K\le 2M$ (Claims 3.2 and 3.3): a shortest tour, shortcut to the points of $R$, has length at least $|R|\tau$.
-- source:
--   Azarmehr–Behnezhad 2026, Metric TSP in Sublinear Time: Breaking Two Approximation, https://arxiv.org/abs/2611.04283, §5.2, p.16 (PDF p.18), size of the r-net; §2.2.1, p.5.

import Mathlib
import Definitions.Def_DoublingMST_IsMetric
import Definitions.Def_DoublingMST_mstWeight

namespace MetricTSPSublinear

/-- **Size of an r-net.** Azarmehr, Behnezhad, *Metric TSP in Sublinear Time: Breaking Two Approximation*,
arXiv:2611.04283, §5.2, p.16 (PDF p.18): "We remark r-net has a size |N| = O(M̂/r) = O(n^{1−a/10}), since there
exists a Hamiltonian cycle of length at most O(M̂)." (also §2.2.1, p.5: "any r-net N satisfies |N| ≤ O(M/r)").

If at least two points are pairwise at distance `≥ τ ≥ 0`, then their number times `τ` is at most `2M`.

**Formalization Note.** The paper's `O(·)` is made explicit with constant `2`, via `TSP ≤ M + K ≤ 2M`; an r-net
(pairwise distances `> r`) satisfies the hypothesis with `τ = r`. -/
theorem net_size_bound {n : ℕ} (d : Fin n → Fin n → ℝ) (hd : DoublingMST.IsMetric d)
    (R : Finset (Fin n)) (τ : ℝ) (hτ : 0 ≤ τ) (hR2 : 2 ≤ R.card)
    (hR : ∀ a ∈ R, ∀ b ∈ R, a ≠ b → τ ≤ d a b) :
    (R.card : ℝ) * τ ≤ 2 * DoublingMST.mstWeight d := by sorry

end MetricTSPSublinear
