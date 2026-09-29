-- Prove2me | Theorems.Thm_KServer_chunk_pad3
-- name    : KServer.chunk_pad3
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-01T23:13:38.967381+00:00
-- url     : https://prove2.me/theorems/eba96fbb-6fc7-480b-b803-518c8cf54295
-- title:
--   Chunk padding with the recursion invariants
-- statement:
--   Chunk padding carrying the full recursion invariants: any chunk system with sizes in $[0, c_B]$, a trivial initial history, total-variance at most $V$, L1-sturdiness (expected Doob drawdown of the total at most $D$ at depths up to $n_0$), and expected below-floor chunk counts at most $B$ at depths up to $n_0$, can be modified so that every chunk is nonempty, preserving the chunk count exactly and all of the listed invariants. The padding replaces empty chunks by a repeat of the last consumed request set and does not change the sample space, measure, filtration, or sizes, so every invariant transfers verbatim.
-- source:
--   Bansal-Cohen-Ravi style randomized k-server lower bound: level recursion plumbing

import Mathlib
import Definitions.Def_KServer_evader
import Definitions.Def_KServer_evader_bail
import Definitions.Def_KServer_chunk_system_b
import Definitions.Def_KServer_chunk_cond
import Definitions.Def_KServer_chunk_stopping
import Definitions.Def_KServer_chunk_adjust
import Definitions.Def_KServer_sturdy

namespace KServer

theorem chunk_pad3 {X : Type*} [MetricSpace X] {s t : X} {cB T pe : ℝ}
    {mL : ℕ} (C : ChunkSystemB X s t 0 cB T pe mL)
    {V D B flo : ℝ} {n₀ : ℕ}
    (hpe0 : 0 ≤ pe)
    (h0triv : ∀ ω₁ ω₂ : C.Ω, C.hist 0 ω₁ = C.hist 0 ω₂)
    (hVar : ∑ ω, C.P ω * ((∑ i, C.size ω i)
      - ∑ ω', C.P ω' * ∑ i, C.size ω' i) ^ 2 ≤ V)
    (hst : C.SturdyL1 n₀ D)
    (hbad : ∀ n ≤ n₀, ∑ ω, C.P ω * (∑ i ∈ Finset.range n,
        if C.sizeN i ω < flo then (1 : ℝ) else 0) ≤ B) :
    ∃ C' : ChunkSystemB X s t 0 cB T pe mL,
      C'.m = C.m ∧
      (∀ ω₁ ω₂ : C'.Ω, C'.hist 0 ω₁ = C'.hist 0 ω₂) ∧
      (∑ ω, C'.P ω * ((∑ i, C'.size ω i)
          - ∑ ω', C'.P ω' * (∑ i, C'.size ω' i)) ^ 2 ≤ V) ∧
      (∀ (ω : C'.Ω) (i : Fin C'.m), C'.chunk ω i ≠ []) ∧
      C'.SturdyL1 n₀ D ∧
      (∀ n ≤ n₀, ∑ ω, C'.P ω * (∑ i ∈ Finset.range n,
          if C'.sizeN i ω < flo then (1 : ℝ) else 0) ≤ B) := by
  sorry

end KServer
