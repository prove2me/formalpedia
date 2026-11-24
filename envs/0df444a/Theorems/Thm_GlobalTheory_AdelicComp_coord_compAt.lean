-- Prove2me | Theorems.Thm_GlobalTheory_AdelicComp_coord_compAt
-- name    : GlobalTheory.AdelicComp.coord_compAt
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T10:53:41.793942+00:00
-- url     : https://prove2.me/theorems/a65f5929-3302-42ee-a25f-2e2cd5f7b7ab
-- title:
--   Adelic Comp: coord comp At
-- statement:
--   The Adelic Comp construction uses the coord comp At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/EqZeroOfCompAtEqZero.lean#L9-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/EqZeroOfCompAtEqZero.lean#L9-L20

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GaloisLevelStructure_DefsAut
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_EqZeroOfCompAtEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2
open scoped TensorProduct
open GlobalTheory GlobalTheory.AdelicComp

theorem GlobalTheory.AdelicComp.coord_compAt (L : Type) [Field L] [NumberField L] [IsCMField L] {ι : Type} [DecidableEq ι] [Finite ι]
    (b : Module.Basis ι (maximalRealSubfield L) L)
    (w : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (i : ι) (z : AL L) :
    TensorProduct.lid (maximalRealSubfield L) _ ((b.coord i).rTensor _ (compAt L w z))
      = evalAt L w (TensorProduct.lid (maximalRealSubfield L) _ ((b.coord i).rTensor _ z)) := by sorry
