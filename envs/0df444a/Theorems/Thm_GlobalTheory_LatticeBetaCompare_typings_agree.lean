-- Prove2me | Theorems.Thm_GlobalTheory_LatticeBetaCompare_typings_agree
-- name    : GlobalTheory.LatticeBetaCompare.typings_agree
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T17:29:44.116635+00:00
-- url     : https://prove2.me/theorems/4a2b60c4-4b01-5d22-860f-94150d7bd279
-- title:
--   Lattice Beta Compare: typings agree
-- statement:
--   The Lattice Beta Compare construction uses the typings agree property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/MultAddMultConjugate.lean#L557-L589
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/MultAddMultConjugate.lean#L557-L589

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_ReflexNormIndexIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsMulMemOfMemSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsCoeEqSpanDetOfIntVecLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_MultAddMultConjugate
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
open GlobalTheory GlobalTheory.LatticeBetaCompare
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice GlobalTheory.IndefiniteRowSideFullHecke.ReflexNormIndexIdeal GlobalTheory.GenusLatCompare
open scoped nonZeroDivisors Pointwise
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}
variable {H : Host E} (Dw : Datum H) {l : Level H} (c : Coeff l)
variable {Dw c}
variable (Dw c)

theorem GlobalTheory.LatticeBetaCompare.typings_agree (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (c : Coeff l) :
    (∀ (n : ℕ) (Λ : Lat E n),
      Submodule.span (𝓞 E) (detSet (toGen Λ).Ln) = latIdeal Λ • Submodule.span (𝓞 E) (detSet (toGen Λ).La) ∧
      ((toGen Λ).Ln.toAddSubgroup.addSubgroupOf (toGen Λ).La.toAddSubgroup).index = Ideal.absNorm (latIdeal Λ) ∧
      (∀ τ, idealAt c (toGen Λ).Ln τ =
        IsLocalization.coeSubmodule c.F ((latIdeal Λ).map (RingOfIntegers.mapRingHom (embF c τ))) *
          idealAt c (toGen Λ).La τ) ∧
      (∀ β, BetaIs (Dw := Dw) c (toGen Λ) β ↔
        ∃ b : 𝓞 c.F, (b : c.F) = β ∧ Ideal.span {b} = reflexIdeal Dw c (latIdeal Λ)) ∧
      (∀ β, BetaAbs (Dw := Dw) c (toGen Λ) β ↔
        ∀ s : c.F →+* ℂ, ‖s β‖ ^ 2 = (Ideal.absNorm (latIdeal Λ) : ℝ) ^ (Dw.p + Dw.q)) ∧
      (∀ β, (β ≠ 0 ∧ BetaIs (Dw := Dw) c (toGen Λ) β ∧ BetaAbs (Dw := Dw) c (toGen Λ) β) ↔ IsBeLat Dw c Λ β) ∧
      (∀ hK : ReflexLe Dw c, ∃ ζ : c.F, IsOfFinOrder ζ ∧ betaH (Dw := Dw) c (toGen Λ) = ζ * be hK Λ) ∧
      (∀ (n' : ℕ) (Λ' : Lat E n'), latIdeal Λ = latIdeal Λ' →
        betaH (Dw := Dw) c (toGen Λ) = betaH (Dw := Dw) c (toGen Λ')) ∧
      (Λ.InGenus → (toGen Λ).Unimod)) ∧
    (KPsiIn (Dw := Dw) c ↔ ReflexLe Dw c) ∧
    (KPsiIn (Dw := Dw) c ↔ ReflexRoots Dw c) ∧
    (ReflexBasis Dw c → KPsiIn (Dw := Dw) c) ∧
    (∀ n bad, BetaExists (Dw := Dw) c n bad ↔
      (ReflexLe Dw c → ∀ Λ : Lat E n, Λ.SelfDual → Λ.StdAt bad → ∃ β : c.F, IsBeLat Dw c Λ β)) ∧
    ((∀ n, BetaExists (Dw := Dw) c n 1) → BeExists Dw c) ∧
    (GenusIffSelfDual H → (BeExists Dw c ↔
      (ReflexBasis Dw c → ∀ (n bad : ℕ) (Λ : GenLat E n), Λ.Unimod → Λ.TrivAt bad →
        ∃ β : c.F, β ≠ 0 ∧ BetaIs (Dw := Dw) c Λ β ∧ BetaAbs (Dw := Dw) c Λ β))) := by sorry
