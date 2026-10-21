-- Prove2me | Theorems.Thm_ModernConvex_PathFollowing_close_duality_gap
-- name    : ModernConvex.PathFollowing.close_duality_gap
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:34:47.78508+00:00
-- url     : https://prove2.me/theorems/b6b2f2ff-0130-4644-8159-a2dfc1244462
-- title:
--   Proposition 6.4.2 (SDP case) — near the central path the duality gap is at most 2k/t
-- statement:
--   Let $\mathcal L$ be a linear subspace of the space $\mathbf S^k$ of real symmetric $k \times k$ matrices ($k \ge 1$), $B, C \in \mathbf S^k$, and consider the primal-dual pair of semidefinite programs $\min\{\operatorname{Tr}(CX) : X \in (\mathcal L - B) \cap \mathbf S^k_+\}$, $\max\{\operatorname{Tr}(BS) : S \in (\mathcal L^\perp + C) \cap \mathbf S^k_+\}$, $\mathcal L^\perp$ the Frobenius-orthogonal complement of $\mathcal L$ in $\mathbf S^k$. Let $X$ and $S$ be strictly feasible solutions ($X \in \mathcal L - B$, $S \in \mathcal L^\perp + C$, $X, S \succ 0$) and $t > 0$ with
--
--   $$\operatorname{dist}((X,S), Z_*(t)) = \|tX^{1/2}SX^{1/2} - I\|_2 \le 1 \qquad \text{(Close)}.$$
--
--   Then the duality gap $\operatorname{DualityGap}(X,S) = \operatorname{Tr}(CX) - \operatorname{Tr}(BS) + \operatorname{Tr}(CB)$ equals $\operatorname{Tr}(XS)$, and
--
--   $$\operatorname{Tr}(XS) \le \frac{2k}{t} \qquad (6.4.12).$$
--
--   Since the duality gap on the central path is $k/t$ in the SDP case, a pair close to the path is, up to a factor 2, as good as the corresponding point of the path.
--
--   **Formalization Note** The book states Proposition 6.4.2 for every canonical cone $\mathbf K$ with parameter $\theta(\mathbf K)$ and verifies it in the SDP case on p. 396; this item is that SDP case ($\mathbf K = \mathbf S^k_+$, $\theta = k$). The middle term $2\,\operatorname{DualityGap}(Z_*(t))$ of (6.4.12) is replaced by its value $2k/t$ (Proposition 6.4.1), so the central path itself is not needed. The distance is its SDP closed form (6.4.11).
-- source:
--   Ben-Tal & Nemirovski, Lectures on Modern Convex Optimization, SIAM 2001, pp. 395–396, Proposition 6.4.2 and (6.4.12), SDP case (verified on p. 396)

import Mathlib
import Definitions.Def_ModernConvex_PathFollowing_SDP

open Matrix
open scoped MatrixOrder

namespace ModernConvex.PathFollowing

/-- Ben-Tal–Nemirovski, Proposition 6.4.2, pp. 395–396, in the SDP case `K = Sᵏ₊` (verified on
p. 396, `θ(K) = k`): if `(X, S)` is a pair of strictly feasible solutions of `(P)`, `(D)` and
`t > 0` with `dist((X, S), Z∗(t)) = ‖tX^{1/2}SX^{1/2} − I‖₂ ≤ 1` (Close), then
`DualityGap(X, S) = Tr(XS) ≤ 2k/t` (6.4.12). -/
theorem close_duality_gap {k : ℕ} (hk : 0 < k) (P : SDPPair k) (X S : Matrix (Fin k) (Fin k) ℝ)
    (hX : P.StrictlyPrimalFeasible X) (hS : P.StrictlyDualFeasible S) (t : ℝ) (ht : 0 < t)
    (hclose : centralPathDist t X S ≤ 1) :
    P.dualityGap X S = (X * S).trace ∧ (X * S).trace ≤ 2 * (k : ℝ) / t := by sorry

end ModernConvex.PathFollowing
