-- Prove2me | Theorems.Thm_GlobalTheory_PowGerm_NabJet_coeff_foldr_DofN_congr
-- name    : GlobalTheory.PowGerm.NabJet.coeff_foldr_DofN_congr
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T18:55:46.402795+00:00
-- url     : https://prove2.me/theorems/48fe4301-57a8-4792-88d9-23fbb3f592e7
-- title:
--   Nab Jet: coeff foldr Dof N congr
-- statement:
--   The Nab Jet construction uses the coeff foldr Dof N congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ConstantCoeffDmonNCongr.lean#L59-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ConstantCoeffDmonNCongr.lean#L59-L73

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_JetsOnCopiesCompatibleFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ConstantCoeffDmonNCongr
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
open GlobalTheory GlobalTheory.PowGerm GlobalTheory.PowGerm.NabJet
open MvPowerSeries
variable {k : Type} [CommRing k] {d n : ℕ}

theorem GlobalTheory.PowGerm.NabJet.coeff_foldr_DofN_congr (F : Fin d → PS k 2 d) {Ix : Type} (cp : Ix → Fin n) (u : Ix → Fin d → k) (m : Ix → ℕ)
    (f g : PS k n d) (L : List Ix) :
    ∀ N : ℕ,
      (∀ mo : Fin n × Fin d →₀ ℕ, mo.degree ≤ N + (L.map m).sum → coeff mo f = coeff mo g) →
      ∀ mo : Fin n × Fin d →₀ ℕ, mo.degree ≤ N →
        coeff mo (L.foldr (fun l s => (DofN F (cp l) (u l))^[m l] s) f) =
          coeff mo (L.foldr (fun l s => (DofN F (cp l) (u l))^[m l] s) g) := by sorry
