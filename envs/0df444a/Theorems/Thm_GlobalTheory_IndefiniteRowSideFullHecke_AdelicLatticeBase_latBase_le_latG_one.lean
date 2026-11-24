-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_AdelicLatticeBase_latBase_le_latG_one
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.AdelicLatticeBase.latBase_le_latG_one
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T17:16:33.933146+00:00
-- url     : https://prove2.me/theorems/81785519-4e5e-45a8-8ca4-81a3718d161c
-- title:
--   Adelic Lattice Base: lat Base le lat G one
-- statement:
--   The Adelic Lattice Base construction uses the lat Base le lat G one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/ExistenceTori/LatticeEmbeddingHalf.lean#L38-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/ExistenceTori/LatticeEmbeddingHalf.lean#L38-L42

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_UnFree
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_LatticeEmbeddingHalf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.AdelicLatticeBase
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open scoped TensorProduct
variable (F : Type) [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [IsCMField E] [Algebra F E]
  {W : Type} [AddCommGroup W] [Module E W] [Module (𝓞 E) W] [IsScalarTower (𝓞 E) E W] {n r : ℕ}
variable (fr : Module.Basis (Fin n) E W) (L : Submodule (𝓞 E) W) (𝔄 : Submodule (𝓞 E) E)
omit [NumberField E] [IsCMField E] [IsScalarTower (𝓞 E) E W]

theorem GlobalTheory.IndefiniteRowSideFullHecke.AdelicLatticeBase.latBase_le_latG_one : latBase L 𝔄 ≤ latG F fr L 𝔄 1 := by sorry
