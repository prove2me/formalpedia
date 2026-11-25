-- Prove2me | Theorems.Thm_GlobalTheory_ThetaLeast_exists_lift_integers
-- name    : GlobalTheory.ThetaLeast.exists_lift_integers
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T00:48:51.903023+00:00
-- url     : https://prove2.me/theorems/2eede215-c4b5-440e-bd77-2ba82568bdaa
-- title:
--   Theta Least: exists lift integers
-- statement:
--   The Theta Least construction uses the exists lift integers property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsCombinationIntegers.lean#L68-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsCombinationIntegers.lean#L68-L76

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_PlaceBelow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_NabValNMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsIntegralCombinationOfMemHaO
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_VVAlgebraMapNonnegDvr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsCombinationIntegers
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open scoped BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj NumberField
open GlobalTheory GlobalTheory.ThetaLeast

theorem GlobalTheory.ThetaLeast.exists_lift_integers (K : Type) [Field K] [NumberField K] (V L : Type) [CommRing V] [IsDomain V]
    [IsIntegrallyClosed V] [Field L] [Algebra V L] [IsFractionRing V L] (io : K →+* L) :
    ∃ φ : 𝓞 K →+* V, ∀ x : 𝓞 K, algebraMap V L (φ x) = io (x : K) := by sorry
