-- Prove2me | Theorems.Thm_KServer_evader_to_server_offline
-- name    : KServer.evader_to_server_offline
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-01T08:51:48.743841+00:00
-- url     : https://prove2.me/theorems/2dd22ac1-bab3-4bce-9e94-24628c1e26cc
-- title:
--   The k-server to evader reduction on k+1 points (offline direction)
-- statement:
--   Let $M$ be a metric space with exactly $k+1$ points, $C_0$ an injective initial configuration of $k$ servers, and $x_0$ its hole (the unique uncovered point). For every sequence $\sigma$ of nonempty set requests,
--
--   $$c_{\mathrm{OPT}}\bigl(\mathrm{enc}_R(\sigma)\bigr) \;\le\; c^{\mathrm{evader}}_{\mathrm{OPT}}(x_0, \sigma),$$
--
--   where $\mathrm{enc}_R$ encodes each set request $S$ as $R$ passes through $M \setminus S$: the optimal $k$-server cost of the encoded sequence is at most the optimal evader cost.
--
--   ## Role
--
--   This is the offline half of the reduction $C^{k\text{-}\mathrm{SRV}} \ge C^{\mathrm{MSS}}$ on $(k+1)$-point spaces (Bubeck–Coester–Rabani, STOC 2023, Proposition 2.6). Together with the online half (`server_to_evader_reduction`), it transfers a distributional evader lower bound — expected online cost at least $L$ times expected offline cost — to the $k$-server problem on the encoded sequences, with the same $L$ up to a constant factor.
--
--   ## Proof idea
--
--   The servers *shadow the complement of the evader*: given a feasible evader path $P$ with $P_j \in S_j$, the schedule keeps the servers on $M \setminus \{P_j\}$ during the $j$-th block, moving a single server (the one standing on $P_{j+1}$) at each block boundary, at cost $d(P_j, P_{j+1})$. Every request of block $j$ lies in $M \setminus S_j \subseteq M \setminus \{P_j\}$, so the blocks are served without further motion. Formally the bound factors through the work function: the covered stretches are free (iterating `workFn_covered`), the boundary moves are paid by the Lipschitz property (`workFn_lipschitz`), the base case is `workFn_nil`, and `offlineCost_le_workFn` concludes. The complement configurations are maintained by an explicit one-update recursion whose invariant — injectivity, and range equal to the complement of the evader's position — is proved by induction with a counting argument for the initial hole.
-- source:
--   Folklore; S. Bubeck, C. Coester, Y. Rabani, 'The randomized k-server conjecture is false!', STOC 2023, Proposition 2.6, offline direction.

import Mathlib
import Definitions.Def_KServer_model
import Definitions.Def_KServer_workfunction
import Definitions.Def_KServer_evader
import Definitions.Def_KServer_evader_encoding

namespace KServer

theorem evader_to_server_offline (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M] [Fintype M]
    (hcard : Fintype.card M = k + 1) (R : ℕ)
    (C₀ : Config k M) (hinj : Function.Injective C₀)
    (x₀ : M) (hx₀ : x₀ ∉ Set.range C₀)
    (σ : List (Set M)) (hσ : ∀ S ∈ σ, S.Nonempty) :
    offlineCost C₀ (encSeq M R σ) ≤ evaderOfflineCost x₀ σ := by sorry

end KServer
