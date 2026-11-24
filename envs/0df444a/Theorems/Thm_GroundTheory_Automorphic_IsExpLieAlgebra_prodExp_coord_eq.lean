-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_prodExp_coord_eq
-- name    : GroundTheory.Automorphic.IsExpLieAlgebra.prodExp_coord_eq
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T23:31:13.201856+00:00
-- url     : https://prove2.me/theorems/6dd54f0a-0991-4e75-acfd-15051f8381b9
-- title:
--   Is Exp Lie Algebra: prod Exp coord eq
-- statement:
--   The Is Exp Lie Algebra construction uses the prod Exp coord eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinHaarCoord.lean#L216-L238
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinHaarCoord.lean#L216-L238

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinBasic
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinHaarCoord
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open scoped Manifold ContDiff Topology
open NormedSpace Set Filter
set_option linter.unusedSectionVars false
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
variable {𝔤 : Submodule ℝ 𝔸}
open GroundTheory.Automorphic.IsExpLieAlgebra
variable {G : Subgroup 𝔸ˣ} (h : IsExpLieAlgebra G 𝔤)

theorem GroundTheory.Automorphic.IsExpLieAlgebra.prodExp_coord_eq {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) {T : Set (Fin d → ℝ)}
    {ψ : (Fin d → ℝ) → (Fin d → ℝ)} (hψT : ∀ w ∈ T, prodExpCoord b (ψ w) = w)
    (hN : ∀ w ∈ T, prodExpVal (fun i => (b i : 𝔸)) (ψ w) ∈ h.nhdOne) {y : G}
    (hy : ((y : 𝔸ˣ) : 𝔸) ∈ h.nhdOne) (hyT : logCoord b ((y : 𝔸ˣ) : 𝔸) ∈ T) :
    h.prodExp (⇑b) (ψ (logCoord b ((y : 𝔸ˣ) : 𝔸))) = y := by sorry
