-- Prove2me | Theorems.Thm_GlobalTheory_Mass_SameBad_exists_unimodular
-- name    : GlobalTheory.Mass.SameBad.exists_unimodular
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T07:40:31.546463+00:00
-- url     : https://prove2.me/theorems/abb14142-339f-48b7-9133-01790cdc8acf
-- title:
--   Same Bad: exists unimodular
-- statement:
--   The Same Bad construction uses the exists unimodular property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/DefiniteHermitianIsometricOfSameBadPrimes.lean#L280-L295
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/DefiniteHermitianIsometricOfSameBadPrimes.lean#L280-L295

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_WittExtensionTotallyDefiniteHermitianStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsMaximalIntegralHermitianLatticeOrthonormalStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MaximalHermitianLatticeBadPrimesIffGramDetStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemHcompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocDual
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_DefiniteHermitianIsometricOfSameBadPrimes
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
open GlobalTheory GlobalTheory.Mass GlobalTheory.Mass.SameBad
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]

theorem GlobalTheory.Mass.SameBad.exists_unimodular [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (hK : IsCMUnram K) {h : V →ₗ⋆[K] V →ₗ[K] K} {β : K} (hs : (ext h β).IsSymm) (hp : PD (ext h β))
    {n : ℕ} (b : Module.Basis (Fin n) K V)
    (hP : ∀ P : Ideal (𝓞 K), P.IsMaximal → conjIdeal (K := K) P = P →
      NormUnit P ((Matrix.of fun i l => h (b i) (b l)).det * β)) :
    ∃ L : Submodule (𝓞 K) (V × K), Submodule.IsLattice K L ∧ IsUnimodular (ext h β) L := by sorry
