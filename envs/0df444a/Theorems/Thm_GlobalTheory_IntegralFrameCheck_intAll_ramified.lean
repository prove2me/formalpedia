-- Prove2me | Theorems.Thm_GlobalTheory_IntegralFrameCheck_intAll_ramified
-- name    : GlobalTheory.IntegralFrameCheck.intAll_ramified
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:10:56.433294+00:00
-- url     : https://prove2.me/theorems/84e69c60-06ba-4226-b124-88c243a3a9b6
-- title:
--   Integral Frame Check: int All ramified
-- statement:
--   The Integral Frame Check construction uses the int All ramified property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/LevelGroupExamples/VVAlgebraMapNonneg.lean#L117-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/LevelGroupExamples/VVAlgebraMapNonneg.lean#L117-L131

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IntAllFree
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_VVAlgebraMapNonneg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IntegralFrameCheck
open Formalism.L2.Pj NumberField IsDedekindDomain
open scoped WithZero
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem GlobalTheory.IntegralFrameCheck.intAll_ramified {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (h : Formalism.L2.PjFree.IntAll Xo c)
    (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ) (ho : OverLa la T.V io e)
    (hf : T.FinRes) (y : letI := io.toAlgebra; FrPt Xo c T.Fr) :
    ∃ (T' : CDVR) (io' : c.F →+* T'.Fr) (r : ℕ) (y' : IntFr Xo c T' io'), 0 < r ∧ OverLa la T'.V io' (r * e) ∧
      T'.FinRes ∧
      letI := io.toAlgebra; letI := io'.toAlgebra
      ∃ (φ : T.Fr →ₐ[c.F] T'.Fr) (z : FrPt Xo c T'.Fr) (t : Ix Dw → T'.Frˣ),
        (∀ x, vV T'.V (φ x) = (r : ℤ) * vV T.V x) ∧ (∀ x, nval T'.V (r * e) (φ x) = nval T.V e x) ∧
        FrMap φ y z ∧ FrBor t z y'.1 := by sorry
