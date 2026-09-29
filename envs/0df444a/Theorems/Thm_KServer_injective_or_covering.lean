-- Prove2me | Theorems.Thm_KServer_injective_or_covering
-- name    : KServer.injective_or_covering
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-31T07:34:25.95041+00:00
-- url     : https://prove2.me/theorems/a7b5ff79-8e24-403e-bf03-a3517176f821
-- title:
--   Either $k$ servers fit on $k$ distinct points, or they can cover the whole space
-- statement:
--   Let $M$ be any type and $k$ any number of servers, and suppose at least one configuration $C_0:\{1,\dots,k\}\to M$ exists.
--
--   **Statement.** Either some configuration is **injective** — its $k$ servers occupy $k$ distinct points — or some configuration **covers** $M$, meaning every point of $M$ carries a server.
--
--   **Role.** This is the dichotomy that lets the analysis of the $k$-server problem on an arbitrary metric space be split into its two genuinely different regimes. When $M$ has at least $k$ points, an injective configuration exists, and the whole classical theory applies: work functions, the Work Function Algorithm kept injective, and the bounds on the growth of the work function. When it does not — that is, when $M$ is finite with fewer than $k$ points — the problem is degenerate: the servers can be parked so as to occupy every point at once, after which no request ever forces a move, so the total cost of the algorithm is a constant and every competitive ratio is achieved trivially.
--
--   Stating the dichotomy separately means the two regimes never have to be disentangled inside a competitive-analysis argument; a theorem on an arbitrary metric space splits on it once, at the top.
--
--   **Formalization Note** No metric is needed, and neither is finiteness: the proof is an induction on $k$. The empty configuration is injective, which settles $k=0$. At the inductive step, either the shorter configuration is already covering, or it is injective; in the latter case, if some point is missed then appending it keeps the configuration injective, and if no point is missed the shorter configuration was already covering. The hypothesis $C_0$ is used only to know that $M$ is nonempty when $k\ge1$, which is what makes the covering alternative available at all. Coverage is phrased as `∀ x, ∃ i, Y i = x`, matching the model's serving condition, rather than as `Function.Surjective`.
-- source:
--   Model infrastructure for the labelled-configuration formulation of the k-server problem; the classical treatment assumes the metric space has at least k points, as in E. Koutsoupias, The k-server problem (survey), Computer Science Review 3 (2009) 105-118, https://doi.org/10.1016/j.cosrev.2009.04.002, Section 1.

import Mathlib
import Definitions.Def_KServer_model

namespace KServer

theorem injective_or_covering (k : ℕ) (M : Type) (C₀ : Config k M) :
    (∃ X : Config k M, Function.Injective X) ∨
      (∃ Y : Config k M, ∀ x : M, ∃ i, Y i = x) := by sorry

end KServer
