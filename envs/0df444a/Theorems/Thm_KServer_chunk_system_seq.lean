-- Prove2me | Theorems.Thm_KServer_chunk_system_seq
-- name    : KServer.chunk_system_seq
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-01T14:49:59.511511+00:00
-- url     : https://prove2.me/theorems/6113fe27-8c65-472f-8719-e18c64a60002
-- title:
--   Sequential composition of chunk systems at a geodesic junction
-- statement:
--   **Sequential composition of chunk systems at a geodesic junction.** Let $Y$ be a metric space and $a, b, c \in Y$ with $d(a,b) + d(b,c) \le d(a,c)$ (so $b$ lies on a geodesic from $a$ to $c$). Let $C_1$ be a chunk system with online escapes from $a$ to $b$ and $C_2$ one from $b$ to $c$, at a common escape price $p_e \ge 0$, with trivial initial histories and size-total variances at most $V_1$ and $V_2$. Then on the product sample space there is a chunk system from $a$ to $c$ whose request sequence is the concatenation of the two phases, with the concatenated chunks and sizes, expected total $T_1 + T_2$, chunk count $m_1 + m_2$, any size window containing both input windows, trivial initial history, and variance at most $V_1 + V_2$: $$\mathrm{Var}\Big(\sum_i c_i\Big) \le V_1 + V_2,$$ by independence of the two phases. The two-phase filtration reveals the first system's history verbatim, then pairs its complete history with the running second-phase history; the second phase's cost premises transfer to the composite by conditioning each evader on the fixed first-phase request prefix, and the offline bound concatenates because the first sequence ends with the pinned singleton request $\{b\}$. This combinator chains the stage constructions of the BCR lower-bound induction along the junctions of the glued level step.
-- source:
--   BCR randomized k-server lower bound, stage construction layer

import Mathlib
import Definitions.Def_KServer_evader
import Definitions.Def_KServer_evader_bail
import Definitions.Def_KServer_chunk_system_b
import Definitions.Def_KServer_bail_append
import Definitions.Def_KServer_shadow

namespace KServer

theorem chunk_system_seq {Y : Type*} [MetricSpace Y] {a b c : Y}
    {cA1 cB1 cA2 cB2 T1 T2 pe : ℝ} {mL1 mL2 : ℕ}
    (C1 : ChunkSystemB Y a b cA1 cB1 T1 pe mL1)
    (C2 : ChunkSystemB Y b c cA2 cB2 T2 pe mL2)
    {cLo cHi V1 V2 : ℝ}
    (hgeo : dist a b + dist b c ≤ dist a c)
    (hpe : 0 ≤ pe)
    (hlo1 : cLo ≤ cA1) (hlo2 : cLo ≤ cA2)
    (hhi1 : cB1 ≤ cHi) (hhi2 : cB2 ≤ cHi)
    (h0triv1 : ∀ ω₁ ω₂ : C1.Ω, C1.hist 0 ω₁ = C1.hist 0 ω₂)
    (h0triv2 : ∀ ω₁ ω₂ : C2.Ω, C2.hist 0 ω₁ = C2.hist 0 ω₂)
    (hVar1 : ∑ ω, C1.P ω * ((∑ i, C1.size ω i)
      - ∑ ω', C1.P ω' * ∑ i, C1.size ω' i) ^ 2 ≤ V1)
    (hVar2 : ∑ ω, C2.P ω * ((∑ i, C2.size ω i)
      - ∑ ω', C2.P ω' * ∑ i, C2.size ω' i) ^ 2 ≤ V2) :
    ∃ C' : ChunkSystemB Y a c cLo cHi (T1 + T2) pe (mL1 + mL2),
      (∀ ω₁ ω₂ : C'.Ω, C'.hist 0 ω₁ = C'.hist 0 ω₂) ∧
      (∑ ω, C'.P ω * ((∑ i, C'.size ω i)
          - ∑ ω', C'.P ω' * (∑ i, C'.size ω' i)) ^ 2 ≤ V1 + V2) := by sorry

end KServer
