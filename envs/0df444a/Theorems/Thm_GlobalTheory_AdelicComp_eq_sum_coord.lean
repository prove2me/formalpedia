-- Prove2me | Theorems.Thm_GlobalTheory_AdelicComp_eq_sum_coord
-- name    : GlobalTheory.AdelicComp.eq_sum_coord
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T10:54:08.608648+00:00
-- url     : https://prove2.me/theorems/eeb69ec2-bf32-477d-8a6e-874c2ec4ea0f
-- title:
--   Adelic Comp: eq sum coord
-- statement:
--   The Adelic Comp construction uses the eq sum coord property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/EqZeroOfCompAtEqZero.lean#L22-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/EqZeroOfCompAtEqZero.lean#L22-L32

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

theorem GlobalTheory.AdelicComp.eq_sum_coord {K V M : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup M] [Module K M]
    {ι : Type} [Fintype ι] (b : Module.Basis ι K V) (z : V ⊗[K] M) :
    z = ∑ i, b i ⊗ₜ[K] TensorProduct.lid K M ((b.coord i).rTensor M z) := by sorry
