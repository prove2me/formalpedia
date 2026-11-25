-- Prove2me | Theorems.Thm_GlobalTheory_exists_sections_span_affine
-- name    : GlobalTheory.exists_sections_span_affine
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:45:26.195608+00:00
-- url     : https://prove2.me/theorems/de7e42ef-f008-4095-9db8-e8a27bf4d991
-- title:
--   Global Theory: exists sections span affine
-- statement:
--   The Global Theory construction uses the exists sections span affine property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsSectionsSpanAffine.lean#L565-L632
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsSectionsSpanAffine.lean#L565-L632

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSectionsSpanAffine
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section
open GlobalTheory.SecAff

theorem GlobalTheory.exists_sections_span_affine :
    SecBaseChangeSt → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (n : ℕ), 1 ≤ n → ∀ U : S.Opens, IsAffineOpen U → ∃ (m : ℕ) (b : Fin (m + 1) → LB.Sec (LPow P.A P.L n (overRes (T := baseOver S) U))), ∀ (T' : Over S) [IsAffine T'.left] (h : T' ⟶ overRes (T := baseOver S) U) (b' : Fin (m + 1) → LB.Sec (LPow P.A P.L n T')), (∀ i, IsPullSec P.A P.L n (h ▷ P.A) (whiskerRight_snd h P.A) (b i) (b' i)) → Submodule.span Γ(T'.left, ⊤) (Set.range fun i => (SecM.ofSec P.A (b' i) : SecM P.A P.L n T')) = ⊤ := by sorry
