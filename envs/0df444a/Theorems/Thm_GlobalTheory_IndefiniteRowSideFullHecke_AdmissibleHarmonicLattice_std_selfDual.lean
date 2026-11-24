-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_AdmissibleHarmonicLattice_std_selfDual
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice.std_selfDual
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T17:15:30.664834+00:00
-- url     : https://prove2.me/theorems/14e1ba28-2404-4ad6-bc38-16ad0c45513b
-- title:
--   Admissible Harmonic Lattice: std self Dual
-- statement:
--   The Admissible Harmonic Lattice construction uses the std self Dual property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/ExistenceTori/AdmissibleHarmonicLattice.lean#L162-L178
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/ExistenceTori/AdmissibleHarmonicLattice.lean#L162-L178

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThProps
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsThRule
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsCombAt
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RowDeg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_AdmissibleHarmonicLattice
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
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj MvPolynomial
open scoped Pointwise
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice.std_selfDual : (Lat.std E n).SelfDual := by sorry
