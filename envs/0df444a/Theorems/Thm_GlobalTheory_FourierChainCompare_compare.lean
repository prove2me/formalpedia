-- Prove2me | Theorems.Thm_GlobalTheory_FourierChainCompare_compare
-- name    : GlobalTheory.FourierChainCompare.compare
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:05:55.500869+00:00
-- url     : https://prove2.me/theorems/d120dfc1-ffa6-58ba-b3f9-1a78671060e1
-- title:
--   Fourier Chain Compare: compare
-- statement:
--   The Fourier Chain Compare construction uses the compare property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/AddCharMemValuationSubring.lean#L379-L400
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/AddCharMemValuationSubring.lean#L379-L400

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_FourierCoeffIntSt
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_PerfectPairings
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_FormalGroupLawCompMulNZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EqZeroOrSingleOfDegreeLtTwo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_AddCharMemValuationSubring
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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB GlobalTheory.IndefiniteRowSideFullHecke.PerfectPairings
open GlobalTheory GlobalTheory.FourierChainCompare

theorem GlobalTheory.FourierChainCompare.compare :
    (∀ (A K : Type) [AddCommGroup A] [Fintype A] [Field K],
      ManyChars A K ↔ ∃ (B : Type) (_ : AddCommGroup B) (_ : Fintype B) (e : A → B → Kˣ),
        IsPerfectPairing e) ∧
    (∀ (A B K : Type) [AddCommGroup A] [AddCommGroup B] [Fintype A] [Fintype B] [Field K]
      (e : A → B → Kˣ), IsPerfectPairing e → ∃ c : B ≃ AddChar A K,
        (∀ t a, c t a = ((e a t : Kˣ) : K)) ∧ ∀ (φ : A → K) (t : B),
          IndefiniteRowSideFullHecke.PerfectPairings.fourierCoeff e φ t = (Fintype.card A : K)⁻¹ * ∑ b, φ b * c t (-b)) ∧
    (FourierInvSt ↔ FourierInversion) ∧
    (EnoughCharacters ↔ ∀ (A K : Type) [AddCommGroup A] [Fintype A] [Field K]
      [HasEnoughRootsOfUnity K (AddMonoid.exponent A)], ManyChars A K) ∧
    (FourierCoeffIntSt → CoeffIntAllChars) ∧ (CoeffIntAllChars ↔ FourierDenominators) ∧
    (∀ (R : Type) [CommRing R] (d : ℕ) (G : FGLaw R d) (n : ℕ), mulN G n = mulNat G n) ∧
    (∀ (R : Type) [CommRing R] (d : ℕ) (G : FGLaw R d) (O : Type) [CommRing O] (A : OAct O G)
      (n : ℕ), A.act (((n : ℤ) : O)) = mulN G n) ∧
    (NChainSt ↔ ChainNat) ∧ (NChainSt → ChainIntOn {n | 0 ≤ n}) ∧
    (NChainSt → (ChainInt ↔ ChainIntOn {-1})) := by sorry
