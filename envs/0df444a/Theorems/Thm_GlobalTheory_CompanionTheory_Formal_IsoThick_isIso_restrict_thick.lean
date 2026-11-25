-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Formal_IsoThick_isIso_restrict_thick
-- name    : GlobalTheory.CompanionTheory.Formal.IsoThick.isIso_restrict_thick
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T07:33:03.438361+00:00
-- url     : https://prove2.me/theorems/c0239dc8-8793-5c3e-9943-9a0981541f5c
-- title:
--   Iso Thick: is Iso restrict thick
-- statement:
--   The Iso Thick construction uses the is Iso restrict thick property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IsoOfThickenings.lean#L291-L310
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IsoOfThickenings.lean#L291-L310

import Mathlib
import Definitions.Def_PositivityTheory_PublishedTheorems_TowerLemmas_FormalTowerLemmas_Imports
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__FormalAlgebraisation_7c2ebf494af3a4ae
import Definitions.Def_PositivityTheory_PublishedTheorems_UnitKilling_UnitAnnihilation_UnitAnnihilators_ExistsUnitKillsOfIdempotent
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IsoOfThickenings
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out PositivityTheory.FormalThickening
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Formal GlobalTheory.CompanionTheory.Formal.IsoThick

theorem GlobalTheory.CompanionTheory.Formal.IsoThick.isIso_restrict_thick {S T : Scheme.{0}} (t : T ⟶ S) (X C : Over S) (p : C ⟶ X)
    (W : X.left.Opens) (g : Over.mk ((p.left ⁻¹ᵁ W).ι ≫ C.hom) ⟶ Over.mk (W.ι ≫ X.hom))
    (hg : g.left = p.left ∣_ W) (h : IsIso ((Over.pullback t).map p).left) :
    IsIso ((Over.pullback t).map g).left := by sorry
