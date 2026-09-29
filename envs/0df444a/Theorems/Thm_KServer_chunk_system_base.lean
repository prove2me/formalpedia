-- Prove2me | Theorems.Thm_KServer_chunk_system_base
-- name    : KServer.chunk_system_base
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-01T09:44:32.400371+00:00
-- url     : https://prove2.me/theorems/bc61d860-53c9-448a-a983-d3d23555b097
-- title:
--   The base case: a chunk system on the path
-- statement:
--   **The base case of BCR's Lemma 6**: on the path of $\beta + 1$ equally spaced points (with $s = 0$, $t = \beta$, so $d(s,t) = \beta$), whenever $\alpha w^2 \le 1$ there is a (deterministic) chunk system with $m = \beta$ chunks: after an initial pinning request $\{0\}$, the $i$-th chunk is the single request $\{i\}$, of size $c_i = 1 \in [\tfrac12, \tfrac32]$. The total size $\beta$ dominates $\alpha w^2 \beta$, and $m = \beta \ge \lceil \alpha\beta w^2 \rceil$.
--
--   The conditional cost bound holds against every evader with escape price $2\beta$: after serving the requests $\{0\}, \dots, \{i-1\}$ the evader's position is pinned at $i - 1$, so serving $\{i\}$ costs exactly $1$, while bailing out costs $2\beta \ge 1$; the first chunk costs at least $1$ from any starting position because it pins the evader at $0$ before requesting $\{1\}$. The offline evader serves everything for cost $\beta$ by walking down the path.
--
--   ## Role
--
--   This is the induction base of the Bubeck–Coester–Rabani $\Omega(\log^2 k)$ lower bound (STOC 2023, Section 4): all levels $w$ with $\alpha w^2 \le 1$ use this path system; the six-copy cyclic construction then builds the higher levels.
--
--   ## Formalization note
--
--   The path metric is induced from the embedding into ℝ. The first chunk is $[\{0\}, \{1\}]$ rather than $[\{1\}]$, pinning the start (the evader model has no distinguished starting point); the sequence convention "first request $\{s\}$" matches BCR.
-- source:
--   S. Bubeck, C. Coester, Y. Rabani, 'The randomized k-server conjecture is false!', STOC 2023, Lemma 6 (base case).

import Mathlib
import Definitions.Def_KServer_evader
import Definitions.Def_KServer_chunk_system

namespace KServer

theorem chunk_system_base (β : ℕ) (hβ : 1 ≤ β) (α : ℝ) (hα0 : 0 ≤ α) (w : ℕ)
    (hw : α * (w : ℝ) ^ 2 ≤ 1) :
    letI := pathMetric β
    dist (0 : Fin (β + 1)) (Fin.last β) = β ∧
    Nonempty (ChunkSystem (Fin (β + 1)) 0 (Fin.last β)
      (1 / 2) (3 / 2) (α * (w : ℝ) ^ 2 * β) (2 * β) ⌈α * β * (w : ℝ) ^ 2⌉₊) := by sorry

end KServer
