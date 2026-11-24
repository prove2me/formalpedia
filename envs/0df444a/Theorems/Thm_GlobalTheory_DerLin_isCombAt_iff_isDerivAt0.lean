-- Prove2me | Theorems.Thm_GlobalTheory_DerLin_isCombAt_iff_isDerivAt0
-- name    : GlobalTheory.DerLin.isCombAt_iff_isDerivAt0
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T20:12:48.004447+00:00
-- url     : https://prove2.me/theorems/5688419d-9bfe-4269-a8de-2238b7bb40aa
-- title:
--   Der Lin: is Comb At iff is Deriv At0
-- statement:
--   The Der Lin construction uses the is Comb At iff is Deriv At0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/IsCombAtIffIsDerivAt0.lean#L50-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/IsCombAtIffIsDerivAt0.lean#L50-L76

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExponentialDerivativeAtZeroIsTangentStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DerivativeAlongTangentCombinationModuliStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsTangentModuleUniversalGroupStatement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_UnivFrame
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_NormConst
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CuspFree
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RdOrbIntOfLatZ
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Landherr__ExistsNormTensor_9eff20d6b37353d0
import Definitions.Def_Development_AbelianVarietyTheory_Statements_HyperbolicHypotheses_HypothesesInhabitedHyperbolic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsCombAtIffIsDerivAt0
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors
open GlobalTheory GlobalTheory.DerLin

theorem GlobalTheory.DerLin.isCombAt_iff_isDerivAt0 : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (σ' : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ' ty) (k : Fin F.n) (P : (F.Di k).La →+ (Fin g → ℂ)), IsPeriod (F.Di k) ty P → ∀ (m : ℕ) (v : Fin m → (Sp (DualNumber ℂ) ⟶ Xo.univ.t.G.left)) (w : Fin m → (Fin g → ℂ)), (∀ i, IsDerivAt0 (fun z => (F.ex k P z).left) (w i) (v i)) → ∀ (a : Fin m → ℂ) (v' : (Sp (DualNumber ℂ) ⟶ Xo.univ.t.G.left)), IsCombAt (F.u k P) v a v' ↔ IsDerivAt0 (fun z => (F.ex k P z).left) (∑ i, a i • w i) v' := by sorry
