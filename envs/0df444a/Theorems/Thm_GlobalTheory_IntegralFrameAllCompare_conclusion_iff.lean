-- Prove2me | Theorems.Thm_GlobalTheory_IntegralFrameAllCompare_conclusion_iff
-- name    : GlobalTheory.IntegralFrameAllCompare.conclusion_iff
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T01:05:13.164422+00:00
-- url     : https://prove2.me/theorems/0c0be183-db5d-4459-9f1c-a712e0888683
-- title:
--   Integral Frame All Compare: conclusion iff
-- statement:
--   The Integral Frame All Compare construction uses the conclusion iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/VVNonnegIffLeOne.lean#L159-L177
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/VVNonnegIffLeOne.lean#L159-L177

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IntAllFree
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_IntegralFrameAcquisition
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_VVNonnegIffLeOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open GlobalTheory GlobalTheory.IntegralFrameAllCompare
open NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.IntegralFrameAcquisition
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} (Xo : Moduli Dw l) (c : Coeff l)

theorem GlobalTheory.IntegralFrameAllCompare.conclusion_iff (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ)
    (ho : OverLa la T.V io e) (y : (letI := io.toAlgebra; FrPt Xo c T.Fr)) :
    (∃ (T' : CDVR) (io' : c.F →+* T'.Fr) (e' : ℕ) (y' : IntFr Xo c T' io'), OverLa la T'.V io' e' ∧ y'.IsAlg ∧
        letI := io.toAlgebra; letI := io'.toAlgebra
        ∃ (φ : T.Fr →ₐ[c.F] T'.Fr) (z : FrPt Xo c T'.Fr) (t : Ix Dw → T'.Frˣ),
          (∀ a : T.V, φ (algebraMap T.V T.Fr a) ∈ Set.range (algebraMap T'.V T'.Fr)) ∧
            FrMap φ y z ∧ FrBor t z y'.1) ↔
      AcquiresIntegralFrame la e y := by sorry
