-- Prove2me | Theorems.Thm_KServer_exists_lazy_injective_algorithm
-- name    : KServer.exists_lazy_injective_algorithm
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-01T08:37:34.664747+00:00
-- url     : https://prove2.me/theorems/6ed6cecc-fbce-4555-9708-7a1b43efd571
-- title:
--   Every k-server algorithm is dominated by a lazy simple one
-- statement:
--   Every deterministic online $k$-server algorithm whose initial configuration places the servers on $k$ distinct points is dominated by one that is **lazy and simple**: starting from the same configuration and never paying more on any request sequence, the dominating algorithm keeps its servers on $k$ distinct points at all times, moves nothing when a request is already covered, and otherwise moves exactly one server, directly onto the request.
--
--   ## Role
--
--   This strengthens the classical laziness reduction (`exists_lazy_algorithm`) by additionally maintaining injectivity of the configurations. On a space of $k+1$ points, a simple configuration leaves exactly one point uncovered — the *hole* — and a lazy simple algorithm moves precisely when the hole is requested, paying the distance the hole travels. This makes the $k$-server problem on $k+1$ points literally the evader problem (metrical service systems), which is the reduction underlying the Bubeck–Coester–Rabani $\Omega(\log^2 k)$ randomized lower bound.
--
--   ## Proof idea
--
--   The dominating algorithm simulates $\mathcal{A}$ while maintaining the potential $\Phi = $ the minimum-cost perfect matching between its configuration and $\mathcal{A}$'s. On a covered request it stays (and $\Phi$ grows by at most $\mathcal{A}$'s step cost, since the matching cost is $1$-Lipschitz). On an uncovered request $r$ it moves the server matched to a server of $\mathcal{A}$ standing on $r$; the move costs exactly the matched edge, which the new matching saves, so the step cost plus the new potential is at most the old potential plus $\mathcal{A}$'s step cost. Telescoping with $\Phi_0 = 0$ dominates the total cost. Injectivity is preserved because the moved server lands on a previously uncovered point.
--
--   ## Formalization note
--
--   Laziness is expressed by the last two conjuncts: no motion on covered requests, and a one-server update otherwise. The minimum-cost matching ranges over permutations of `Fin k`.
-- source:
--   Classical (implicit in M. Manasse, L. McGeoch, D. Sleator 1990 and standard k-server surveys: configurations may be assumed simple and algorithms lazy); needed for the hole/evader reduction of S. Bubeck, C. Coester, Y. Rabani, STOC 2023.

import Mathlib
import Definitions.Def_KServer_model

namespace KServer

theorem exists_lazy_injective_algorithm (k : ℕ) (M : Type*) [MetricSpace M]
    (A : OnlineAlgorithm k M) (hinj : Function.Injective (A.conf [])) :
    ∃ B : OnlineAlgorithm k M,
      B.conf [] = A.conf [] ∧
      (∀ σ : List M, B.cost σ ≤ A.cost σ) ∧
      (∀ l : List M, Function.Injective (B.conf l)) ∧
      (∀ (l : List M) (r : M), (∃ i, B.conf l i = r) → B.conf (l ++ [r]) = B.conf l) ∧
      (∀ (l : List M) (r : M), ∃ i : Fin k, B.conf (l ++ [r]) = Function.update (B.conf l) i r) := by sorry

end KServer
