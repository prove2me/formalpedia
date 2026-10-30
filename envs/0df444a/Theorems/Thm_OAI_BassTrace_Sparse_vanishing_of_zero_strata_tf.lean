-- Prove2me | Theorems.Thm_OAI_BassTrace_Sparse_vanishing_of_zero_strata_tf
-- name    : OAI.BassTrace.Sparse.vanishing_of_zero_strata_tf
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T23:08:27.320724+00:00
-- url     : https://prove2.me/theorems/f7518af1-dcd1-438d-a2ab-9d52561d7864
-- title:
--   OAI.BassTrace.Sparse.vanishing_of_zero_strata_tf: intermediate lemma from OpenAI, The Bass trace conjecture and the characteristic-zero Kaplansky idempotent conjecture
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.TorsionFreeBass.torsion_free_corollary`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Bass trace conjecture and the characteristic-zero Kaplansky idempotent conjecture*, OpenAI Math Release, September 24, 2026, result family 207, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.BassTrace.Sparse.vanishing_of_zero_strata` of [lean/OAI/RingTheory/BassTrace/SparseBounds.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RingTheory/BassTrace/SparseBounds.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.BassTrace.Sparse`, with `open Set MeasureTheory`, `open Finset MeasureTheory intervalIntegral`, `open Set Finset MeasureTheory`, `open scoped BassTrace.Sparse Classical`, `open Oriented ChainHomotopy Fundamental BarycentricChains SubdivisionChains GraphGeometry`):
--
--   ```lean
--   lemma vanishing_of_zero_strata_tf
--       (hInv : (augmentedComplex K).IsInvariant (H := H))
--       (hμ : ∀h : H,MeasurePreserving (fun x : X=>h • x) μ μ)
--       (C : SourceTop K n → ℝ) (hC : ∀σ,0≤C σ)
--       (hzero : ∀ε : ℝ,0<ε → ∃Q : OrbitForms.SeparatingFiltration (H := H) (X := X)
--         (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K)
--         (realizationDistance Γ hΓ K n) R n,
--         ∀σ : SourceTop K n,(∫x,(Measure.count ((Q.pair 0).P.val x∩
--           convexHull ℝ (simplexVertices σ.val : Set (Y →₀ ℝ)))).toReal ∂μ)≤C σ*ε)
--       (ψ : Degree Y (n+1) →ₗ[ℂ] ℂ)
--       (hψ : ∀(h : H) c,ψ (relabel (n+1) (fun y=>h • y) c)=ψ c)
--       (hψd : ∀c,ψ (d (n+1) c)=0)
--       (c : (augmentedComplex K).chains (n+1))
--       (hc : (⟨d n c,(augmentedComplex K).d_mem n c.property⟩ :
--         (augmentedComplex K).chains n)∈(augmentedComplex K).relations hInv n) : ψ c=0
--   ```
--
--   **Definitions.** The statement is written with `OAI.BassTrace.ChainHomotopy.d`, `OAI.BassTrace.ChainHomotopy.relabel`, `OAI.BassTrace.Oriented.Degree`, `OAI.BassTrace.Sparse.SourceTop`, `OAI.BassTrace.Sparse.augmentedComplex`, `OAI.BassTrace.Sparse.realFinsuppNormedAddCommGroup`, `OAI.BassTrace.Sparse.realFinsuppNormedSpace`, `OAI.BassTrace.Sparse.simplexVertices`, `OAI.BassTrace.ChainHomotopy.Complex.IsInvariant`, `OAI.BassTrace.ChainHomotopy.Complex.chains`, `OAI.BassTrace.ChainHomotopy.Complex.d_mem`, `OAI.BassTrace.ChainHomotopy.Complex.relations`, `OAI.BassTrace.Sparse.GraphGeometry.realizationDistance`, `OAI.BassTrace.Sparse.OrbitForms.SeparatingFiltration`, `OAI.BassTrace.Sparse.Cuts.MarkedFamily` and `OAI.BassTrace.Sparse.OrbitForms.MarkedPair` (definitions bundle `OAIQ113B000` of this split); `OAI.BassTrace.Sparse.instMeasurableSpaceFinsuppReal_solutions_3` (definitions bundle `OAIQ113B002` of this split).
--
--   **Used by.** The proofs of `OAI.TorsionFreeBass.scalar_trace_eq_augmentation_tf` and `OAI.TorsionFreeBass.torsion_free_corollary` of this split import it.
-- source:
--   OpenAI, The Bass trace conjecture and the characteristic-zero Kaplansky idempotent conjecture, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 207; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Bass-trace-conjecture-for-complex-group-rings-September-24-2026/The-Bass-trace-conjecture-for-complex-group-rings-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RingTheory/BassTrace/SparseBounds.lean (declaration OAI.BassTrace.Sparse.vanishing_of_zero_strata)

import Mathlib
import Definitions.Def_OAIQ113B002

section

attribute [-instance] _root_.OAI.BassTrace.RightProjective.rightModuleIdentityRingHomInvPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
open Finset MeasureTheory intervalIntegral
noncomputable section

namespace BassTrace.Sparse

open Set Finset MeasureTheory

open scoped BassTrace.Sparse Classical

open Oriented ChainHomotopy Fundamental BarycentricChains SubdivisionChains GraphGeometry

variable {H Y X : Type*} [Group H] [MulAction H Y] [LinearOrder Y]
  [LinearOrder (Y →₀ ℝ)] [TopologicalSpace X] [MulAction H X]
  [CompactSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]

variable {K : PreAbstractSimplicialComplex Y} {n : ℕ} {R : ℝ}

variable (Γ : SimpleGraph Y) [Γ.LocallyFinite] (hΓ : Γ.Connected)

variable (hK : ∀ s∈K.faces,∃ σ∈K.faces,s⊆σ ∧ σ.card=n+1 ∧
  (Γ.induce (σ : Set Y)).Connected)

variable (hn : 0<n) (hR : 0≤R) (y₀ : Y)

variable (μ : Measure X) [IsProbabilityMeasure μ]

attribute [local instance] OAI.BassTrace.Sparse.instMeasurableSpaceFinsuppReal_solutions_3
local instance instBorelSpaceFinsuppReal_solutions_3_r5c79b7_1 : BorelSpace (Y →₀ ℝ) := ⟨rfl⟩
include hK hn hR y₀ in
lemma vanishing_of_zero_strata_tf
    (hInv : (augmentedComplex K).IsInvariant (H := H))
    (hμ : ∀h : H,MeasurePreserving (fun x : X=>h • x) μ μ)
    (C : SourceTop K n → ℝ) (hC : ∀σ,0≤C σ)
    (hzero : ∀ε : ℝ,0<ε → ∃Q : OrbitForms.SeparatingFiltration (H := H) (X := X)
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K)
      (realizationDistance Γ hΓ K n) R n,
      ∀σ : SourceTop K n,(∫x,(Measure.count ((Q.pair 0).P.val x∩
        convexHull ℝ (simplexVertices σ.val : Set (Y →₀ ℝ)))).toReal ∂μ)≤C σ*ε)
    (ψ : Degree Y (n+1) →ₗ[ℂ] ℂ)
    (hψ : ∀(h : H) c,ψ (relabel (n+1) (fun y=>h • y) c)=ψ c)
    (hψd : ∀c,ψ (d (n+1) c)=0)
    (c : (augmentedComplex K).chains (n+1))
    (hc : (⟨d n c,(augmentedComplex K).d_mem n c.property⟩ :
      (augmentedComplex K).chains n)∈(augmentedComplex K).relations hInv n) : ψ c=0 := by
  sorry

end BassTrace.Sparse

end

end OAI
end
