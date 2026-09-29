-- Prove2me | Theorems.Thm_KServer_chunk_blocks3
-- name    : KServer.chunk_blocks3
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-02T01:47:35.636884+00:00
-- url     : https://prove2.me/theorems/20f01e23-da34-41b1-95ac-bca582741303
-- title:
--   Fixed-block regrouping with fractional-tiling prophecy pass-through
-- statement:
--   Fixed-block regrouping with start-measurable prophecy pass-through. Identical to the fixed-block regrouping theorem chunk_blocks (blocks of b consecutive chunks with deterministic boundaries min(k*b, m), output sizes the conditional block masses, expected total preserved exactly, variance at most 2V + 2CV, L1-sturdiness through with additive sqrt(CV), below-floor count reset by Markov), with the prophecy hypothesis strengthened to the start-measurable fractional-tiling form: the input system satisfies ProphecyBoundS PE, and the regrouped system satisfies ProphecyBoundS PE with the same constant. The pass-through blows each block-level window family up to chunk depth: windows [bIdx(aa i), bIdx(bb i)) with tails cut at bIdx(jj i), the same weights (measurable at the blown-up window starts, which coincide since bIdx saturates at m), and the fractional-tiling condition transported through the block map H mapsto H/b. Inside each block cell the weighted square splits exactly into per-depth weighted energies by weighted orthogonality of the Doob increments, since each weight is measurable at its own window start, at or before every cell.
-- source:
--   Bartal-Chrobak-Rasala lower bound program: block regrouping with prophecy energy

import Mathlib
import Definitions.Def_KServer_evader
import Definitions.Def_KServer_evader_bail
import Definitions.Def_KServer_chunk_system_b
import Definitions.Def_KServer_chunk_cond
import Definitions.Def_KServer_chunk_stopping
import Definitions.Def_KServer_chunk_var
import Definitions.Def_KServer_sturdy
import Definitions.Def_KServer_prophecy
import Definitions.Def_KServer_prophecyS

namespace KServer

theorem chunk_blocks3 {X : Type*} [MetricSpace X] {s t : X}
    {cA cB T pe : ℝ} {mL : ℕ} (C : ChunkSystemB X s t cA cB T pe mL)
    {b M n₀ : ℕ} {p' V CV D B flo θ PE : ℝ}
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
    (hθ : 0 < θ) (hflo : 0 < flo)
    (hPPE : C.ProphecyBoundS PE) :
    ∃ C' : ChunkSystemB X s t 0 ((b : ℝ) * cB) T p' M,
      C'.m = M ∧
      (∀ ω₁ ω₂ : C'.Ω, C'.hist 0 ω₁ = C'.hist 0 ω₂) ∧
      (∑ ω, C'.P ω * ((∑ i, C'.size ω i)
          - ∑ ω', C'.P ω' * (∑ i, C'.size ω' i)) ^ 2
        ≤ 2 * V + 2 * CV) ∧
      C'.SturdyL1 n₀ (D + Real.sqrt CV) ∧
      (∀ n ≤ n₀, ∑ ω, C'.P ω * (∑ i ∈ Finset.range n,
          if C'.sizeN i ω < (1 - θ) * ((b : ℝ) * flo)
          then (1 : ℝ) else 0) ≤ B / (θ * (b : ℝ))) ∧
      C'.ProphecyBoundS PE := by
  sorry

end KServer
