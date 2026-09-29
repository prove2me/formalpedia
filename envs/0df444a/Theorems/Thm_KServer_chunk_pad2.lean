-- Prove2me | Theorems.Thm_KServer_chunk_pad2
-- name    : KServer.chunk_pad2
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-01T20:47:54.538259+00:00
-- url     : https://prove2.me/theorems/7647bb24-d990-431a-b1d1-f9f8ef30c5fb
-- title:
--   Chunk padding with preserved chunk count
-- statement:
--   A strengthening of the chunk-padding lemma that additionally records that the number of chunks is unchanged. Any chunk system with sizes in $[0, c_B]$, a trivial initial history, and total-variance at most $V$ can be modified so that every chunk is a nonempty request list, preserving the number of chunks exactly ($C'.m = C.m$), the expected total, the price, the trivial initial history, and the variance bound. The exact chunk count is needed downstream to bound range terms in variance estimates of systems built from the padded one.
-- source:
--   Bansal-Cohen-Ravi style randomized k-server lower bound: level recursion plumbing

import Mathlib
import Definitions.Def_KServer_evader
import Definitions.Def_KServer_evader_bail
import Definitions.Def_KServer_chunk_system_b

namespace KServer

theorem chunk_pad2 {X : Type*} [MetricSpace X] {s t : X} {cB T pe : ℝ}
    {mL : ℕ} (C : ChunkSystemB X s t 0 cB T pe mL) {V : ℝ}
    (hpe0 : 0 ≤ pe)
    (h0triv : ∀ ω₁ ω₂ : C.Ω, C.hist 0 ω₁ = C.hist 0 ω₂)
    (hVar : ∑ ω, C.P ω * ((∑ i, C.size ω i)
      - ∑ ω', C.P ω' * ∑ i, C.size ω' i) ^ 2 ≤ V) :
    ∃ C' : ChunkSystemB X s t 0 cB T pe mL,
      C'.m = C.m ∧
      (∀ ω₁ ω₂ : C'.Ω, C'.hist 0 ω₁ = C'.hist 0 ω₂) ∧
      (∑ ω, C'.P ω * ((∑ i, C'.size ω i)
          - ∑ ω', C'.P ω' * (∑ i, C'.size ω' i)) ^ 2 ≤ V) ∧
      (∀ (ω : C'.Ω) (i : Fin C'.m), C'.chunk ω i ≠ []) := by sorry

end KServer
