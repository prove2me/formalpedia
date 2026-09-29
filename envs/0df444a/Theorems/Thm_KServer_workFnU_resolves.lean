-- Prove2me | Theorems.Thm_KServer_workFnU_resolves
-- name    : KServer.workFnU_resolves
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-31T22:07:34.627395+00:00
-- url     : https://prove2.me/theorems/370d13b8-b663-408b-b7e2-58d7cfc5ff05
-- title:
--   Every configuration resolves after a request
-- statement:
--   Let $w$ be the (unlabelled) work function of a $k$-server instance whose request sequence ends with the request $r$. Then every configuration $X = x_1 \dots x_k$ **resolves**: there is a server $x_i$ with
--
--   $$w(X) \;=\; w\bigl(X - x_i + r\bigr) \;+\; d(x_i, r).$$
--
--   The inequality $\le$ is $1$-Lipschitzness of $w$ and holds for every $i$; the content is that for some $i$ it is an equality --- an optimal offline solution ending at $X$ can be taken to pass through the configuration $X - x_i + r$ and then move that single server out to $x_i$.
--
--   ## Role
--
--   This is the defining structural property of the class $\mathcal W^k(r)$ of work functions "after a request $r$" in the framework of Coester and Koutsoupias, and it is the engine of their case analyses. When one asks *which* server of a configuration resolves, one obtains a partition of the possibilities on which their proofs for multi-ray spaces, trees and the circle are organised; the anchor-swapping lemma, the monotonicity of resolution, and the final case analysis for three servers on trees all begin by naming the server from which a given configuration resolves. The property is also what makes the potential method computable: it turns the work function of a fresh request into a finite minimum of shifted values of the previous one.
--
--   Two familiar facts sit on either side of it. A configuration that already contains $r$ resolves trivially, with $d(x_i,r) = 0$ and the work function unchanged by the request. And the minimum of $w$ over all configurations containing $r$ is attained one server-move away from an unconstrained minimiser --- the greedy substitution property --- which is the same phenomenon seen from the side of minimisers rather than of arbitrary configurations.
--
--   ## Formalization note
--
--   $w$ is `workFnU`, the work function of an *unlabelled* configuration, obtained from the labelled one by minimising over the relabellings of the target; the statement is false for the labelled work function, whose value at a configuration depends on which server is asked to stand where. Configurations are functions $\mathrm{Fin}\,k \to M$ and $X - x_i + r$ is `Function.update X i r`. No finiteness, boundedness or compactness hypothesis on the metric space is required, and $\sigma$ may be any request prefix; only $k \ge 1$ is assumed.
-- source:
--   The defining property of the class W^k(r) in C. Coester, E. Koutsoupias, 'Towards the k-server conjecture: a unifying potential, pushing the frontier to the circle', ICALP 2021, arXiv:2102.10474, Preliminaries; the underlying recurrence is that of E. Koutsoupias, C. H. Papadimitriou, 'On the k-server conjecture', JACM 42 (1995).

import Mathlib
import Definitions.Def_KServer_workfunctionU

namespace KServer

theorem workFnU_resolves (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (r : M) (X : Config k M) :
    ∃ i : Fin k, workFnU C₀ (σ ++ [r]) X
      = workFnU C₀ (σ ++ [r]) (Function.update X i r) + dist r (X i) := by sorry

end KServer
