-- Prove2me | Theorems.Thm_GroundTheory_Brauer_H2mul_coe_relBrauerEquiv
-- name    : GroundTheory.Brauer.H2mul.coe_relBrauerEquiv
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T09:43:43.295504+00:00
-- url     : https://prove2.me/theorems/b6bcaa70-7b93-400e-a307-82eb8200f839
-- title:
--   H2mul: coe rel Brauer Equiv
-- statement:
--   The H2mul construction uses the coe rel Brauer Equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/CrossedProductIso.lean#L330-L331
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/CrossedProductIso.lean#L330-L331

import Mathlib
import Definitions.Def_GroundTheory_Brauer_CrossedProduct
import Definitions.Def_GroundTheory_Brauer_CrossedProductSimple
import Definitions.Def_GroundTheory_Brauer_CrossedProductMaps
import Definitions.Def_GroundTheory_Brauer_CrossedProductInj
import Definitions.Def_GroundTheory_Brauer_CrossedProductTensor
import Definitions.Def_GroundTheory_Brauer_SkolemNoether
import Definitions.Def_GroundTheory_Brauer_DoubleCentralizer
import Definitions.Def_GroundTheory_Brauer_Splitting
import Definitions.Def_GroundTheory_Brauer_BaseChange
import Definitions.Def_GroundTheory_Brauer_IsBrauerEquivalentIffNonemptyAlgEquiv
import Definitions.Def_GroundTheory_Brauer_MulDistribMulActionQuotientFixedPoints
import Definitions.Def_GroundTheory_Brauer_CrossedProductIso
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
open TensorProduct Module groupCohomology
universe u
variable {K L : Type u} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
open GroundTheory.Brauer.H2mul

theorem GroundTheory.Brauer.H2mul.coe_relBrauerEquiv (x : H2mul (L ≃ₐ[K] L) Lˣ) :
    (relBrauerEquiv K L x : BrauerGroup.{u, u} K) = toBrauer K L x := by sorry

attribute [defeq] GroundTheory.Brauer.H2mul.coe_relBrauerEquiv
