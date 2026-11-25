-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_WedgeEmb_laplace
-- name    : GlobalTheory.CompanionTheory.WedgeEmb.laplace
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:26:26.338113+00:00
-- url     : https://prove2.me/theorems/8ace3cf1-8407-4e1b-b879-5a31968020f1
-- title:
--   Wedge Emb: laplace
-- statement:
--   The Wedge Emb construction uses the laplace property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/ExteriorIntegrality.lean#L88-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/ExteriorIntegrality.lean#L88-L109

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_IsSimpleFam
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ExteriorIntegrality
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.WedgeEmb
variable {n m : ℕ}

theorem GlobalTheory.CompanionTheory.WedgeEmb.laplace (g : Matrix (Fin n) (Fin n) ℂ) (r : Fin (m + 1) → Fin n) (i : Fin (m + 1))
    (J : BranchingSupport.Sub n m) (hJ : ⇑(J.1.orderEmbOfFin J.2) = fun a => r (i.succAbove a)) (I : BranchingSupport.Sub n (m + 1)) :
    ((cmp m g ⊗ₖ g) * jW n m) (J, r i) I =
      (-1) ^ (i : ℕ) * (g.submatrix r (I.1.orderEmbOfFin I.2)).det := by sorry
