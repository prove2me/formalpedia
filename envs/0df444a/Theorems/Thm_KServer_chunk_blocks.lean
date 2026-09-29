-- Prove2me | Theorems.Thm_KServer_chunk_blocks
-- name    : KServer.chunk_blocks
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-01T23:26:40.003112+00:00
-- url     : https://prove2.me/theorems/df02f792-7b9d-43b2-aad9-d270f3223d67
-- title:
--   Fixed-block regrouping preserving total, variance, sturdiness, and floor counts
-- statement:
--   Fixed-block regrouping of a chunk system. Given a chunk system C with m chunks, group the chunks into M blocks of b consecutive chunks each (the last block possibly shorter, with deterministic boundaries min(k*b, m)). The output system C' has exactly M chunks; the size of block k is the conditional expectation of the block's total mass given the history at the block's start. The theorem asserts existence of the regrouped system with: (1) exactly M chunks; (2) trivial time-0 history; (3) variance at most 2V + 2CV, where V bounds the input variance and CV bounds the sum over blocks of the expected squared deviation of block mass from its conditional expectation at block start (the block conditional variance budget, a hypothesis); (4) the L1 sturdiness (expected Doob drawdown) invariant passes through with additive correction sqrt(CV), by orthogonality of the per-block corrections; (5) the below-floor block count: if at most B expected input chunks lie below floor flo (up to depth n0*b), then at most B/(theta*b) expected output blocks lie below (1-theta)*b*flo, by Markov's inequality applied to the conditional below-floor count within a block. Chunk costs: output bail cost cLo' = 0, cHi' = b*cB, price p' at least pe + b*cB.
-- source:
--   Bartal-Chrobak-Rasala lower bound program: block regrouping step

import Mathlib
import Definitions.Def_KServer_evader
import Definitions.Def_KServer_evader_bail
import Definitions.Def_KServer_chunk_system_b
import Definitions.Def_KServer_chunk_cond
import Definitions.Def_KServer_chunk_stopping
import Definitions.Def_KServer_sturdy

namespace KServer

theorem chunk_blocks {X : Type*} [MetricSpace X] {s t : X}
    {cA cB T pe : ℝ} {mL : ℕ} (C : ChunkSystemB X s t cA cB T pe mL)
    {b M n₀ : ℕ} {p' V CV D B flo θ : ℝ}
    (hb0 : 0 < b) (hM0 : 0 < M) (hMm : M ≤ C.m)
    (hcov : C.m ≤ M * b) (hlastblk : (M - 1) * b < C.m)
    (hn₀M : n₀ + 1 ≤ M)
    (hcA0 : 0 ≤ cA) (hcB0 : 0 ≤ cB) (hpe : 0 ≤ pe)
    (hp : pe + (b : ℝ) * cB ≤ p')
    (h0triv : ∀ ω₁ ω₂ : C.Ω, C.hist 0 ω₁ = C.hist 0 ω₂)
    (hVar : ∑ ω, C.P ω * ((∑ i, C.size ω i)
      - ∑ ω', C.P ω' * ∑ i, C.size ω' i) ^ 2 ≤ V)
    (hCV : ∑ k ∈ Finset.range M, ∑ ω, C.P ω
      * ((∑ i ∈ Finset.Ico (min (k * b) C.m) (min ((k + 1) * b) C.m),
            C.sizeN i ω)
        - C.condExp (fun ω' =>
            ∑ i ∈ Finset.Ico (min (k * b) C.m) (min ((k + 1) * b) C.m),
              C.sizeN i ω') (min (k * b) C.m) ω) ^ 2 ≤ CV)
    (hCV0 : 0 ≤ CV)
    (hst : C.SturdyL1 (n₀ * b) D)
    (hbad : ∀ n ≤ n₀ * b, ∑ ω, C.P ω * (∑ i ∈ Finset.range n,
        if C.sizeN i ω < flo then (1 : ℝ) else 0) ≤ B)
    (hθ : 0 < θ) (hflo : 0 < flo) :
    ∃ C' : ChunkSystemB X s t 0 ((b : ℝ) * cB) T p' M,
      C'.m = M ∧
      (∀ ω₁ ω₂ : C'.Ω, C'.hist 0 ω₁ = C'.hist 0 ω₂) ∧
      (∑ ω, C'.P ω * ((∑ i, C'.size ω i)
          - ∑ ω', C'.P ω' * (∑ i, C'.size ω' i)) ^ 2
        ≤ 2 * V + 2 * CV) ∧
      C'.SturdyL1 n₀ (D + Real.sqrt CV) ∧
      (∀ n ≤ n₀, ∑ ω, C'.P ω * (∑ i ∈ Finset.range n,
          if C'.sizeN i ω < (1 - θ) * ((b : ℝ) * flo)
          then (1 : ℝ) else 0) ≤ B / (θ * (b : ℝ))) := by
  sorry

end KServer
