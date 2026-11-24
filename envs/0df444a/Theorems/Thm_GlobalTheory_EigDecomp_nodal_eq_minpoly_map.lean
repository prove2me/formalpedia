-- Prove2me | Theorems.Thm_GlobalTheory_EigDecomp_nodal_eq_minpoly_map
-- name    : GlobalTheory.EigDecomp.nodal_eq_minpoly_map
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T12:53:26.088012+00:00
-- url     : https://prove2.me/theorems/e0e8e62c-e423-4b78-99f0-07d1b86ade1d
-- title:
--   Eig Decomp: nodal eq minpoly map
-- statement:
--   The Eig Decomp construction uses the nodal eq minpoly map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsUniqueEmbeddingEigenspaceSum.lean#L48-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsUniqueEmbeddingEigenspaceSum.lean#L48-L65

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
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H}

theorem GlobalTheory.EigDecomp.nodal_eq_minpoly_map (c : Coeff l) (α : 𝓞 E)
    (hinj : Function.Injective fun τ : E →+* ℂ => embK c τ α) :
    Lagrange.nodal Finset.univ (fun τ : E →+* ℂ => embK c τ α) = (minpoly ℤ α).map (Int.castRingHom c.F) := by sorry
