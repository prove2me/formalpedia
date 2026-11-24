-- Prove2me | Theorems.Thm_GlobalTheory_T_nablaValueCopies_bilinear
-- name    : GlobalTheory.T.nablaValueCopies_bilinear
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T20:54:36.661309+00:00
-- url     : https://prove2.me/theorems/8416abd2-45a7-4864-82bc-e2dbc9cbe7c5
-- title:
--   T: nabla Value Copies bilinear
-- statement:
--   The T construction uses the nabla Value Copies bilinear property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/NablaValueCopiesBilinearStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/NablaValueCopiesBilinearStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_NablaValueCopiesBilinear
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_PlaceBelow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_NablaValueCopiesBilinearStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj NumberField
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.nablaValueCopies_bilinear : ∀ (K : Type) [CommRing K] [Algebra ℚ K] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB K d O) (h : PS K 2 d) (w0 : O) (m n : ℕ) (ι : Type) [Fintype ι] (cp : ι → Fin n) (u : ι → Fin d → K), (∀ (f g : PS K n d) (P : MvPolynomial ι K), nabValN B K h w0 m (f + g) cp u P = nabValN B K h w0 m f cp u P + nabValN B K h w0 m g cp u P) ∧ (∀ (t : K) (f : PS K n d) (P : MvPolynomial ι K), nabValN B K h w0 m (t • f) cp u P = t * nabValN B K h w0 m f cp u P) ∧ (∀ (f : PS K n d) (P Q : MvPolynomial ι K), nabValN B K h w0 m f cp u (P + Q) = nabValN B K h w0 m f cp u P + nabValN B K h w0 m f cp u Q) ∧ (∀ (t : K) (f : PS K n d) (P : MvPolynomial ι K), nabValN B K h w0 m f cp u (MvPolynomial.C t * P) = t * nabValN B K h w0 m f cp u P) := by sorry
