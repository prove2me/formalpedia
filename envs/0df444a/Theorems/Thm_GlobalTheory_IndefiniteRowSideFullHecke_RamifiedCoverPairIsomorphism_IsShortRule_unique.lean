-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_RamifiedCoverPairIsomorphism_IsShortRule_unique
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.RamifiedCoverPairIsomorphism.IsShortRule.unique
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:13:13.077598+00:00
-- url     : https://prove2.me/theorems/20e071bb-151e-4406-ae3f-c5426febb487
-- title:
--   Is Short Rule: unique
-- statement:
--   The Is Short Rule construction uses the unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/ExistenceTori/ShortRuleRepresentationChange.lean#L126-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/ExistenceTori/ShortRuleRepresentationChange.lean#L126-L136

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThProps
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThGerm
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_ReflexNormIndexIdeal
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_NormFactorThetaValue
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_DeltaDatumCombinedCoefficient
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_ShortRuleRepresentationChange
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
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.RamifiedCoverPairIsomorphism
open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice GlobalTheory.IndefiniteRowSideFullHecke.ReflexNormIndexIdeal GlobalTheory.IndefiniteRowSideFullHecke.LevelSpanSeparation GlobalTheory.IndefiniteRowSideFullHecke.NormFactorThetaValue GlobalTheory.IndefiniteRowSideFullHecke.DeltaDatumCombinedCoefficient
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} {nab : NabV Xo c} (Δ : DeltaDatum Xo c nab)

theorem GlobalTheory.IndefiniteRowSideFullHecke.RamifiedCoverPairIsomorphism.IsShortRule.unique (h : CoverTot Δ) {n N : ℕ} {Λ : Lat E n} {β : c.F} {x₀ : Fin n → ConjCl Dw l}
    {a : (E →+* ℂ) × ℕ → ℕ} {P : MvPolynomial (LtN Dw n) c.F} (hd : IsSeriesData Δ Λ N β a P) {f g : Rul Xo c}
    (hf : IsShortRule Δ Λ N β x₀ a P f) (hg : IsShortRule Δ Λ N β x₀ a P g) : f = g := by sorry
