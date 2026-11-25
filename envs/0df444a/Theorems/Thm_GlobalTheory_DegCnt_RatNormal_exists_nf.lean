-- Prove2me | Theorems.Thm_GlobalTheory_DegCnt_RatNormal_exists_nf
-- name    : GlobalTheory.DegCnt.RatNormal.exists_nf
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:34:40.007952+00:00
-- url     : https://prove2.me/theorems/5d5e387e-aab8-59cf-8c77-ffcaaa5a1ea7
-- title:
--   Rat Normal: exists nf
-- statement:
--   The Rat Normal construction uses the exists nf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsInvLower.lean#L194-L252
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsInvLower.lean#L194-L252

import Mathlib
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsInvLower
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt Formalism.HermitianLatticeCounting.P
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.RatNormal

theorem GlobalTheory.DegCnt.RatNormal.exists_nf : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (F F' : FlagD H r) (j : ℕ) (hj : j ≤ r) (c : K) (T : ℕ) (𝔡 : Ideal (𝓞 K)) (w : Formalism.MainNotions.S.Loc.Pt K j) (sgn : Fin j → ℤˣ) (A B : Matrix (Fin j) (Fin j) K), NFFull F F' j hj c → F.T = T → F'.T = T → (∀ σ : K →+* ℂ, F.PosDefAt σ) → 𝔡 ≠ ⊥ → (∀ x ∈ 𝔡, ∃ y ∈ 𝔡, (y : K) = star (x : K)) → (∀ a b, a < b → A a b = 0 ∧ B b a = 0) → (∀ a, A a a = 1 ∧ B a a = 1) → ((Zhat F F').submatrix (Fin.castLE (hj.trans (Nat.le_succ r))) (Fin.castLE (hj.trans (Nat.le_succ r))) = A * (Matrix.of fun a b => w.mat a b * ((sgn b : ℤ) : K)) * B) → ∃ N : NF H r, N.j = j ∧ N.c = c ∧ N.T = T ∧ N.𝔡 = 𝔡 ∧ (∀ a, N.F.e a - F.e a ∈ F.Xa a.val) ∧ ∀ a, N.F'.e a - F'.e a ∈ F'.Xa a.val := by sorry
