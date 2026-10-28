-- Prove2me | Theorems.Thm_OAI_Kadison_TracialSequence_exists_freeCornerPosition_of_equiv_stages
-- name    : OAI.Kadison.TracialSequence.exists_freeCornerPosition_of_equiv_stages
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T09:55:38.001071+00:00
-- url     : https://prove2.me/theorems/379e2e85-cae8-466c-8ff4-3512bb6a02ea
-- title:
--   OAI.Kadison.TracialSequence.exists_freeCornerPosition_of_equiv_stages: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.TracialSequence`, with `open scoped Topology ComplexOrder Matrix.Norms.L2Operator`, `open Filter`, `open MatrixTower`):
--
--   ```lean
--   theorem exists_freeCornerPosition_of_equiv_stages [TopologicalSpace.SeparableSpace σ.GNS]
--       (htrace : ∀ a,σ (e a)=τ a)
--       (hτ : ∀ a b : A,τ (a*b)=τ (b*a)) (hσ : ∀ a b : M,σ (a*b)=σ (b*a))
--       (hω : (ω : Filter ℕ) ≤ atTop)
--       (hnormal : NormalGNS.BoundedWOTContinuous M σ)
--       (hfaith : ∀ a : M,σ (star a*a)=0 → a=0) (hone : τ 1=1)
--       (hirr : ∀ b : M,(∀ n a,(E n).hom a*b=b*(E n).hom a) →
--         ∃ c : ℂ,b=algebraMap ℂ M c)
--       (hstage : ∀ n a,((E n).hom a : H →L[ℂ] H)∈R)
--       (hgrow : Tendsto (fun n => (Fintype.card (E n).I:ℝ)) atTop atTop)
--       (hdiffuse : DiffuseProjection.HasNoMinimalProjections R) :
--       Nonempty (FreeCornerPosition τ ω R j)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.NormalGNS.BoundedWOTContinuous` (definitions bundle `OAIQ039C002` of this split); `OAI.Kadison.VonNeumannCStar.starOrderedRing` (definitions bundle `OAIQ039C003` of this split); `OAI.Kadison.DiffuseProjection.HasNoMinimalProjections` (definitions bundle `OAIQ039C008` of this split); `OAI.Kadison.NormalSubalgebra.inclusion` and `OAI.Kadison.VonNeumannCStar.cstarAlgebra` (definitions bundle `OAIQ039C022` of this split); `OAI.Kadison.MatrixTower.Stage` (definitions bundle `OAIQ039C054` of this split); `OAI.Kadison.TracialSequence.FreeCornerPosition` (definitions bundle `OAIQ039C067` of this split).
--
--   **Used by.** The proof of `OAI.Kadison.MatrixTower.exists_matrix_freeCornerPosition` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ039C067

section

attribute [-instance] _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped Topology ComplexOrder Matrix.Norms.L2Operator

open Filter

namespace Kadison.TracialSequence

open MatrixTower

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (M R : VonNeumannAlgebra H) [Nontrivial M] (hRM : R ≤ M)
  (e : A ≃⋆ₐ[ℂ] M) (j : R →⋆ₐ[ℂ] A)
  (hj : ∀ q,e (j q)=NormalSubalgebra.inclusion M R hRM q)

variable (τ : A →ₚ[ℂ] ℂ) (σ : M →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ)

variable (E : ℕ → Stage M) (hE : Monotone (fun n => (E n).hom.range))

include hRM hj hE in
theorem exists_freeCornerPosition_of_equiv_stages [TopologicalSpace.SeparableSpace σ.GNS]
    (htrace : ∀ a,σ (e a)=τ a)
    (hτ : ∀ a b : A,τ (a*b)=τ (b*a)) (hσ : ∀ a b : M,σ (a*b)=σ (b*a))
    (hω : (ω : Filter ℕ) ≤ atTop)
    (hnormal : NormalGNS.BoundedWOTContinuous M σ)
    (hfaith : ∀ a : M,σ (star a*a)=0 → a=0) (hone : τ 1=1)
    (hirr : ∀ b : M,(∀ n a,(E n).hom a*b=b*(E n).hom a) →
      ∃ c : ℂ,b=algebraMap ℂ M c)
    (hstage : ∀ n a,((E n).hom a : H →L[ℂ] H)∈R)
    (hgrow : Tendsto (fun n => (Fintype.card (E n).I:ℝ)) atTop atTop)
    (hdiffuse : DiffuseProjection.HasNoMinimalProjections R) :
    Nonempty (FreeCornerPosition τ ω R j) := by
  sorry

end Kadison.TracialSequence

end

end
end

end OAI
end
