-- Prove2me | Theorems.Thm_GroundTheory_Brauer_CrossedProduct_nonempty_algEquiv_of_isBrauerEquivalent
-- name    : GroundTheory.Brauer.CrossedProduct.nonempty_algEquiv_of_isBrauerEquivalent
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T06:16:15.018802+00:00
-- url     : https://prove2.me/theorems/47084d02-191f-432c-96a5-9ba1fc99a43a
-- title:
--   Crossed Product: nonempty alg Equiv of is Brauer Equivalent
-- statement:
--   The Crossed Product construction uses the nonempty alg Equiv of is Brauer Equivalent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/CrossedProductInj.lean#L119-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/CrossedProductInj.lean#L119-L125

import Mathlib
import Definitions.Def_GroundTheory_Brauer_CrossedProduct
import Definitions.Def_GroundTheory_Brauer_CrossedProductSimple
import Definitions.Def_GroundTheory_Brauer_CrossedProductMaps
import Definitions.Def_GroundTheory_Brauer_SkolemNoether
import Definitions.Def_GroundTheory_Brauer_IsBrauerEquivalentIffNonemptyAlgEquiv
import Definitions.Def_GroundTheory_Brauer_MulDistribMulActionQuotientFixedPoints
import Definitions.Def_GroundTheory_Brauer_CrossedProductInj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Brauer
open groupCohomology
universe u v
open GroundTheory.Brauer.CrossedProduct
variable {K L : Type u} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
variable {f : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ}

theorem GroundTheory.Brauer.CrossedProduct.nonempty_algEquiv_of_isBrauerEquivalent {g : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ}
    (hf : IsMulCocycle₂ f) (hg : IsMulCocycle₂ g)
    (h : IsBrauerEquivalent (csaOf K (CrossedProduct hf)) (csaOf K (CrossedProduct hg))) :
    Nonempty (CrossedProduct hf ≃ₐ[K] CrossedProduct hg) := by sorry
