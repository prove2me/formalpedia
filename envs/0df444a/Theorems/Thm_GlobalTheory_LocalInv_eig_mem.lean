-- Prove2me | Theorems.Thm_GlobalTheory_LocalInv_eig_mem
-- name    : GlobalTheory.LocalInv.eig_mem
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T19:23:41.429466+00:00
-- url     : https://prove2.me/theorems/75ea2f1b-32ba-4082-8419-2c024da64243
-- title:
--   Local Inv: eig mem
-- statement:
--   The Local Inv construction uses the eig mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/WeightRegularOfExt.lean#L198-L225
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/WeightRegularOfExt.lean#L198-L225

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataN
import Definitions.Def_Formalism_LocalRingCardinality_DataRows
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ThetaLiftGeometry_NoLocalInvariants
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ThetaLiftGeometry_TemperedRepresentations
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_WeightRegularOfExt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.LocalInv
open NumberField IsDedekindDomain Polynomial Matrix Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.IndefiniteRowSideFullHecke.NoLocalInvariantsRankParts
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

theorem GlobalTheory.LocalInv.eig_mem (eig : Eig N A) (h1 : EigAway N A eig) (h2 : EigAbove N A eig) (i : N.Loc) {a : ℕ}
    (ρ : G H.E N.Om →* GL (Fin a) (N.O i)) (χ : G H.E N.Om →* (N.O i)ˣ) (hρ : Cont N i ρ)
    (hχ : Cont N i (charRep N i χ)) (w : PlE H)
    (dρ : w ∈ placesOver H.E (N.l i) → DeRham N A i ρ w)
    (dχ : w ∈ placesOver H.E (N.l i) → DeRham N A i (charRep N i χ) w)
    (hs : SubOrQuot N i ρ χ w) (σ : G H.E N.Om) (hσ : FrobLift N w σ) (c : ℂ)
    (hc : eig w (wd N A i (charRep N i χ) w) σ = {c}) : c ∈ eig w (wd N A i ρ w) σ := by sorry
