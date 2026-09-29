-- Prove2me | Theorems.Thm_KServer_chunk_blocks2
-- name    : KServer.chunk_blocks2
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-02T00:11:51.158703+00:00
-- url     : https://prove2.me/theorems/e226e085-e9b2-4aef-bf83-f83ce388c2f9
-- title:
--   Fixed-block regrouping with prophecy pass-through
-- statement:
--   Fixed-block regrouping with prophecy pass-through. Identical to the fixed-block regrouping theorem chunk_blocks (blocks of b consecutive chunks with deterministic boundaries min(k*b, m), output sizes the conditional block masses, expected total preserved exactly, variance at most 2V + 2CV, L1-sturdiness through with additive sqrt(CV), below-floor count reset by Markov), with one additional hypothesis and one additional conclusion: if the input system satisfies the partitioned prophecy energy bound ProphecyBound PE (for every monotone partition of the chunk range, the summed second moments of the Doob increments of the beyond-cell tail masses are at most PE), then so does the output system, with the SAME constant PE. The reason is exact: an output partition blows up to the input partition through the deterministic block boundaries; the output conditional tail masses are the input conditional tail masses at the block starts (tower through the blocks), so each output Doob increment is the sum of the b input Doob increments of the same tail across the corresponding input window, and by orthogonality of Doob increments the output energy equals the input energy of the blown-up partition. Combined with cv_from_ppe (CV <= 2V + 2PE) this closes the conditional-block-variance budget of the regrouping recursion.
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

namespace KServer

theorem chunk_blocks2 {X : Type*} [MetricSpace X] {s t : X}
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
    (hPPE : C.ProphecyBound PE) :
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
      C'.ProphecyBound PE := by
  sorry

end KServer
