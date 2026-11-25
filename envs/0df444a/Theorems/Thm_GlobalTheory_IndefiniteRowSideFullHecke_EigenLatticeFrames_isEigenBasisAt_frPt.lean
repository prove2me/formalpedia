-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_EigenLatticeFrames_isEigenBasisAt_frPt
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.EigenLatticeFrames.isEigenBasisAt_frPt
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:08:56.640152+00:00
-- url     : https://prove2.me/theorems/73649ac9-aa8b-4311-95a1-783aee735a23
-- title:
--   Eigen Lattice Frames: is Eigen Basis At fr Pt
-- statement:
--   The Eigen Lattice Frames construction uses the is Eigen Basis At fr Pt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/HeightDefect/EigenLatticeFrames.lean#L63-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/HeightDefect/EigenLatticeFrames.lean#L63-L65

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_VAtVNeBot
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_HeightDefect_EigenLatticeFrames
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.EigenLatticeFrames
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

theorem GlobalTheory.IndefiniteRowSideFullHecke.EigenLatticeFrames.isEigenBasisAt_frPt {Xo : Moduli Dw l} {c : Coeff l} {S : Type} [CommRing S] [Algebra c.F S]
    (y : FrPt Xo c S) (τ : E →+* ℂ) : IsEigenBasisAt Xo c y.x τ (y.u τ) := by sorry
