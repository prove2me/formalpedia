-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_EigenLatticeFrames_exists_basis_of_integral
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.EigenLatticeFrames.exists_basis_of_integral
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:08:46.046027+00:00
-- url     : https://prove2.me/theorems/eaf1e2b5-cd7a-408c-9aec-37442c6b201b
-- title:
--   Eigen Lattice Frames: exists basis of integral
-- statement:
--   The Eigen Lattice Frames construction uses the exists basis of integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/HeightDefect/EigenLatticeFrames.lean#L67-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/HeightDefect/EigenLatticeFrames.lean#L67-L74

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

theorem GlobalTheory.IndefiniteRowSideFullHecke.EigenLatticeFrames.exists_basis_of_integral {Xo : Moduli Dw l} {c : Coeff l} {T : CDVR} {io : c.F →+* T.Fr}
    (y : letI := io.toAlgebra; FrPt Xo c T.Fr) (h : Integral T io y) :
    letI := io.toAlgebra
    ∃ (G : SAB H (Sp T.V)) (t' : SAB H (Sp T.Fr)) (m₁ : SABMap t' Xo.univ.t y.x)
      (m₂ : SABMap t' G (spMap (algebraMap T.V T.Fr))), ∀ τ, ∃ ub, IsEigenLatticeBasis Dw c T io G τ ub ∧
        ∀ i, IsGenericFibre m₁ m₂ (ub i) (y.u τ i) := by sorry
