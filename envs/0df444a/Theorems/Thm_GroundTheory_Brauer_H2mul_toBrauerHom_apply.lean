-- Prove2me | Theorems.Thm_GroundTheory_Brauer_H2mul_toBrauerHom_apply
-- name    : GroundTheory.Brauer.H2mul.toBrauerHom_apply
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T09:06:56.906266+00:00
-- url     : https://prove2.me/theorems/5565176b-4920-419c-a053-32dd44916b13
-- title:
--   H2mul: to Brauer Hom apply
-- statement:
--   The H2mul construction uses the to Brauer Hom apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/CrossedProductTensor.lean#L284-L284
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/CrossedProductTensor.lean#L284-L284

import Mathlib
import Definitions.Def_GroundTheory_Brauer_CrossedProduct
import Definitions.Def_GroundTheory_Brauer_CrossedProductSimple
import Definitions.Def_GroundTheory_Brauer_CrossedProductMaps
import Definitions.Def_GroundTheory_Brauer_CrossedProductRegular
import Definitions.Def_GroundTheory_Brauer_CrossedProductInj
import Definitions.Def_GroundTheory_Brauer_TensorSimple
import Definitions.Def_GroundTheory_Brauer_IsBrauerEquivalentIffNonemptyAlgEquiv
import Definitions.Def_GroundTheory_Brauer_BaseChangeCSA
import Definitions.Def_GroundTheory_Brauer_BaseChange
import Definitions.Def_GroundTheory_Brauer_MulDistribMulActionQuotientFixedPoints
import Definitions.Def_GroundTheory_Brauer_CrossedProductTensor
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
open groupCohomology TensorProduct
universe u
variable {K L : Type u} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
open GroundTheory.Brauer.H2mul

theorem GroundTheory.Brauer.H2mul.toBrauerHom_apply (x : H2mul (L ≃ₐ[K] L) Lˣ) : toBrauerHom K L x = toBrauer K L x := by sorry

attribute [defeq] GroundTheory.Brauer.H2mul.toBrauerHom_apply
