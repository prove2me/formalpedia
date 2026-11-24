-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_HProj_map_eqs
-- name    : GlobalTheory.CompanionTheory.SW.HProj.map_eqs
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T12:05:38.113212+00:00
-- url     : https://prove2.me/theorems/b42c2ebc-1897-4094-a675-6b8b592cbf5c
-- title:
--   HProj: map eqs
-- statement:
--   The HProj construction uses the map eqs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/AdelicUnitaryGroupProjections.lean#L183-L194
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/AdelicUnitaryGroupProjections.lean#L183-L194

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdelicTupleProjectionsStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdelicUnitaryGroupProjections
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.HProj
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {d : ℕ}

theorem GlobalTheory.CompanionTheory.SW.HProj.map_eqs {R R' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R']
    (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (φ : R →ₐ[F] R')
    (A A' : Matrix (Fin M) (Fin M) (R ⊗[F] E)) (g : HA R' σ J)
    (hA : A.map (tm E φ) = ((HA.mat R' σ J g : GL _ _) : Matrix (Fin M) (Fin M) (R' ⊗[F] E)))
    (hA' : A'.map (tm E φ) = ((HA.mat R' σ J g⁻¹ : GL _ _) : Matrix (Fin M) (Fin M) (R' ⊗[F] E))) :
    (A * A').map (tm E φ) = (1 : Matrix (Fin M) (Fin M) (R ⊗[F] E)).map (tm E φ) ∧
      (cT (sigR R σ) A * JR R J * A).map (tm E φ) = (JR R J).map (tm E φ) := by sorry
