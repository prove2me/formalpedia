-- Prove2me | Theorems.Thm_GlobalTheory_EigDecomp_X_sub_C_mul_basis
-- name    : GlobalTheory.EigDecomp.X_sub_C_mul_basis
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T12:53:14.585526+00:00
-- url     : https://prove2.me/theorems/d0e2f82e-956b-4a5d-ae7e-b258d8a30ba3
-- title:
--   Eig Decomp: X sub C mul basis
-- statement:
--   The Eig Decomp construction uses the X sub C mul basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsUniqueEmbeddingEigenspaceSum.lean#L71-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsUniqueEmbeddingEigenspaceSum.lean#L71-L76

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_EmbKCoe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsUniqueEmbeddingEigenspaceSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor Polynomial IntermediateField
open GlobalTheory GlobalTheory.EigDecomp

theorem GlobalTheory.EigDecomp.X_sub_C_mul_basis {ι F : Type*} [Field F] [DecidableEq ι] {s : Finset ι} {v : ι → F} {i : ι}
    (hi : i ∈ s) :
    (X - C (v i)) * Lagrange.basis s v i = C (Lagrange.nodalWeight s v i) * Lagrange.nodal s v := by sorry
