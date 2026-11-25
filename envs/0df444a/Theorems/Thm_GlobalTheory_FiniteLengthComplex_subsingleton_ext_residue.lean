-- Prove2me | Theorems.Thm_GlobalTheory_FiniteLengthComplex_subsingleton_ext_residue
-- name    : GlobalTheory.FiniteLengthComplex.subsingleton_ext_residue
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:01:48.298591+00:00
-- url     : https://prove2.me/theorems/46211c91-3857-4e0e-a05a-feb537a28a32
-- title:
--   Finite Length Complex: subsingleton ext residue
-- statement:
--   The Finite Length Complex construction uses the subsingleton ext residue property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/AcyclicityLemmaDepthDifferentialCokernelsFiniteL.lean#L110-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/AcyclicityLemmaDepthDifferentialCokernelsFiniteL.lean#L110-L132

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsRegularOfSupportDimQuotientAddLengthLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_AcyclicityLemmaDepthDifferentialCokernelsFiniteL
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian IsLocalRing
open GlobalTheory
open GlobalTheory.FiniteLengthComplex
variable {R : Type} [CommRing R]

theorem GlobalTheory.FiniteLengthComplex.subsingleton_ext_residue [IsRegularLocalRing R] (g : ℕ) (hg : ringKrullDim R = g)
    (n : ℕ) (hn : n ≠ g) :
    Subsingleton
      (Abelian.Ext.{0} (ModuleCat.of R (R ⧸ maximalIdeal R)) (ModuleCat.of R R) n) := by sorry
