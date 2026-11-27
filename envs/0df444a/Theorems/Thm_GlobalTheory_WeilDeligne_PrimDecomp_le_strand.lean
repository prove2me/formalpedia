-- Prove2me | Theorems.Thm_GlobalTheory_WeilDeligne_PrimDecomp_le_strand
-- name    : GlobalTheory.WeilDeligne.PrimDecomp.le_strand
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T17:57:59.86784+00:00
-- url     : https://prove2.me/theorems/c8fed8bf-13c9-44ba-852a-4f2192f7303b
-- title:
--   Prim Decomp: le strand
-- statement:
--   The Prim Decomp construction uses the le strand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/RestrictHomApply.lean#L87-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/RestrictHomApply.lean#L87-L89

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_MonodromyZeroOfWeilDeligneRepClassIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RestrictHomApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module
open GlobalTheory GlobalTheory.WeilDeligne GlobalTheory.WeilDeligne.PrimDecomp
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
variable {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

theorem GlobalTheory.WeilDeligne.PrimDecomp.le_strand (N : End ℂ V) (S : Submodule ℂ V) (m : ℕ) : S ≤ strand N S m := by sorry
