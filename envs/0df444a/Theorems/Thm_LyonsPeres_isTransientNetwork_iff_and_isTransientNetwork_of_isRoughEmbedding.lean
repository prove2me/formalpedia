-- Prove2me | Theorems.Thm_LyonsPeres_isTransientNetwork_iff_and_isTransientNetwork_of_isRoughEmbedding
-- name    : LyonsPeres.isTransientNetwork_iff_and_isTransientNetwork_of_isRoughEmbedding
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-07T09:27:24.419009+00:00
-- url     : https://prove2.me/theorems/502b22f4-7b2e-4841-a554-a710c3d642a6
-- title:
--   Lyons–Peres, Theorem 2.17 (external) — roughly equivalent networks are transient together, and a rough embedding carries transience forward
-- statement:
--   Let $c$ and $c'$ be networks on vertex sets $V$ and $V'$: nonnegative symmetric conductances with $0 < \sum_y c(x, y) < \infty$ at every vertex, connected. A rough embedding $\varphi : V \to V'$ of $c$ into $c'$ consists of constants $\alpha$, $\beta$ and, for every edge $\langle x, y\rangle$ of $c$ with $x \ne y$, a path $\Phi(x, y)$ in $c'$ from $\varphi(x)$ to $\varphi(y)$, with at least one edge and no repeated vertex, whose resistances $1/c'$ sum to at most $\alpha / c(x, y)$, with $\Phi(y, x)$ the reverse of $\Phi(x, y)$, such that each edge of $c'$ is traversed, in a given direction, by the paths of at most $\beta$ ordered edges of $c$. A network is transient when its random walk, started at some vertex, fails to return there with positive probability. Then:
--
--   1. if there are rough embeddings of $c$ into $c'$ and of $c'$ into $c$, then $c$ is transient if and only if $c'$ is;
--   2. if there is a rough embedding of $c$ into $c'$ and $c$ is transient, then $c'$ is transient.
--
--   Lyons and Peres, p. 44: “Theorem 2.17. (Rough Embeddings and Transience) If $G$ and $G'$ are roughly equivalent connected networks, then $G$ is transient iff $G'$ is transient. In fact, if there is a rough embedding from $G$ to $G'$ and $G$ is transient, then $G'$ is transient.”
--
--   Loops of $c$ carry no path condition; Lyons and Peres say of loops that they “may be ignored for our present purposes since they only delay the random walk” (p. 26). The networks satisfy their standing assumption (2.6), that the conductances at each vertex have finite sum (p. 26). Juschenko, Matte Bon, Monod and de la Salle apply the theorem on p. 17 in its contrapositive form: an injective Lipschitz map from a Schreier graph into a recurrent Cayley graph forces the Schreier graph to be recurrent.
-- source:
--   Lyons, R. and Peres, Y., Probability on Trees and Networks, Cambridge University Press, 2016, https://doi.org/10.1017/9781316672815, p. 44, Theorem 2.17, as applied in Juschenko, K., Matte Bon, N., Monod, N. and de la Salle, M., Extensive amenability and an application to interval exchanges, Ergodic Theory Dynam. Systems 38 (2018) 195–219, https://doi.org/10.1017/etds.2016.32 (arXiv:1503.04977v1, whose page numbers are used), p. 17

import Mathlib
import Definitions.Def_IntervalExchange

open IntervalExchange

namespace LyonsPeres

theorem isTransientNetwork_iff_and_isTransientNetwork_of_isRoughEmbedding {V V' : Type*} (c : V → V → ℝ)
    (c' : V' → V' → ℝ) (hc : IsNetwork c) (hc' : IsNetwork c') :
    (∀ (φ : V → V') (ψ : V' → V), IsRoughEmbedding c c' φ → IsRoughEmbedding c' c ψ →
      (IsTransientNetwork c ↔ IsTransientNetwork c')) ∧
    ∀ φ : V → V', IsRoughEmbedding c c' φ → IsTransientNetwork c → IsTransientNetwork c' := by
  sorry

end LyonsPeres
