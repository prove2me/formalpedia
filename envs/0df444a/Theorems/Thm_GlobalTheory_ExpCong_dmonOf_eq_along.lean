-- Prove2me | Theorems.Thm_GlobalTheory_ExpCong_dmonOf_eq_along
-- name    : GlobalTheory.ExpCong.dmonOf_eq_along
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T00:42:56.396131+00:00
-- url     : https://prove2.me/theorems/f835f840-db58-4ea3-a6b3-5e47740fdc7a
-- title:
--   Exp Cong: dmon Of eq along
-- statement:
--   The Exp Cong construction uses the dmon Of eq along property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsGroupedOfSublist.lean#L117-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsGroupedOfSublist.lean#L117-L120

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_DofDApply
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ExpSNegMulExpS
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_MapDofIterate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsGroupedOfSublist
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open GlobalTheory GlobalTheory.ExpCong
variable {k : Type} [CommRing k] {d : ℕ} (F : Fin d → PS k 2 d) {ι : Type} [Fintype ι] (u : ι → Fin d → k)

theorem GlobalTheory.ExpCong.dmonOf_eq_along (m : ι →₀ ℕ) (f : PS k 1 d) :
    DmonOf F u m f =
      along (fun l => Dof F (u l)) (grouped (Finset.univ : Finset ι).toList m).reverse f := by sorry
