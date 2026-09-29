-- Prove2me | Theorems.Thm_KServer_chunk_pad
-- name    : KServer.chunk_pad
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-01T16:54:59.083052+00:00
-- url     : https://prove2.me/theorems/6aefb5b8-1dae-4dc1-8b92-ae731a1a2a30
-- title:
--   Chunk padding: removing empty chunks from a chunk system
-- statement:
--   **Chunk padding** (a technical normalization for the BCR race construction). Let $C$ be a chunk system with online escapes on a metric space $X$ with marked entry $s$ and exit $t$: a finitely supported random sequence of $m$ chunks of set requests with an explicit refining filtration, sizes in $[0, c_B]$, expected total size at least $T$, escape price $p_e \ge 0$, chunk-cost bounds against every evader and every online escape rule, offline cost at most $d(s,t)$, and last request pinned to $\{t\}$. Assume the initial history is trivial and the variance of the total size is at most $V$. Then there is a chunk system $C'$ with the same parameters, the same trivial initial history and the same variance bound $V$, in which **no chunk is the empty list**:
--   $$\forall \omega, \forall i, \quad \mathrm{chunk}'_\omega(i) \neq [\,].$$
--   The construction replaces each empty chunk by a single repeat of the last consumed request (the entry $\{s\}$ if nothing has been consumed). The point of the normalization is that a serving evader's position after any consumed prefix then always lies in the last request of that prefix, which aligns the boundary positions of offset shadow evaders in interleaved constructions. The cost bounds survive because an empty chunk has zero escape cost, so replacing it can only increase the right-hand side of the chunk-cost inequality; the offline cost survives because the inserted repeats are served for free by the path that serves the original sequence; and the pinned ending survives because a trailing empty chunk means the pinned request already occurred earlier in the flattened sequence.
-- source:
--   Technical normalization for the race construction in the BCR randomized k-server lower bound, adapted

import Mathlib
import Definitions.Def_KServer_evader
import Definitions.Def_KServer_evader_bail
import Definitions.Def_KServer_chunk_system_b

namespace KServer

theorem chunk_pad {X : Type*} [MetricSpace X] {s t : X} {cB T pe : ℝ}
    {mL : ℕ} (C : ChunkSystemB X s t 0 cB T pe mL) {V : ℝ}
    (hpe0 : 0 ≤ pe)
    (h0triv : ∀ ω₁ ω₂ : C.Ω, C.hist 0 ω₁ = C.hist 0 ω₂)
    (hVar : ∑ ω, C.P ω * ((∑ i, C.size ω i)
      - ∑ ω', C.P ω' * ∑ i, C.size ω' i) ^ 2 ≤ V) :
    ∃ C' : ChunkSystemB X s t 0 cB T pe mL,
      (∀ ω₁ ω₂ : C'.Ω, C'.hist 0 ω₁ = C'.hist 0 ω₂) ∧
      (∑ ω, C'.P ω * ((∑ i, C'.size ω i)
          - ∑ ω', C'.P ω' * (∑ i, C'.size ω' i)) ^ 2 ≤ V) ∧
      (∀ (ω : C'.Ω) (i : Fin C'.m), C'.chunk ω i ≠ []) := by sorry

end KServer
