-- Prove2me | Theorems.Thm_GlobalTheory_AnVal_rd_mulN
-- name    : GlobalTheory.AnVal.rd_mulN
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-27T05:30:16.830333+00:00
-- url     : https://prove2.me/theorems/99030cb7-b3b9-4d44-b346-688cb5f34c2d
-- title:
--   An Val: rd mul N
-- statement:
--   The An Val construction uses the rd mul N property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/NormalisedPullbackMulNReadsTheta.lean#L116-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/NormalisedPullbackMulNReadsTheta.lean#L116-L157

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ThConst
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_AbelianHolomorphicFrameReadingConstOfFormsCancelStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_GeneratorReadingCorrMulInv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_GeneratorReadingPullbackPeriodRigid
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ReadingTwistedPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_NormalisedPullbackMulNReadsTheta
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
open GlobalTheory GlobalTheory.AnVal
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.AnVal.rd_mulN : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : RigLB A) (x0 : Sp ℂ ⟶ S) (g : ℕ) (Φ : AnFr A L x0 g), ∀ (N : ℕ) (α₀ : LB.Gen (LB.LinComb L.L (K := Fin 2) ![𝟙 A.left, (mulA A N).left] ![(N : ℤ) ^ 2, -1])) (α : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(snd (Over.mk x0) A).left, (snd (Over.mk x0) A ^ N).left] ![(N : ℤ) ^ 2, -1])) (s : LB.Sec (LPow A L.L 1 (Over.mk x0))) (s₁ : LB.Sec (LPow A L.L ((N : ℤ) ^ 2) (Over.mk x0))) (θ : (Fin g → ℂ) → ℂ), α₀.IsGen → IsNormMul A L.L L.rig N α₀ → LB.Gen.Corr L.L _ _ _ _ α (LB.pullGen L.L _ _ α₀ (snd (Over.mk x0) A).left) → IsTwistPull A L.L (mulT A (Over.mk x0) N) (snd (Over.mk x0) A ^ N) (lift_snd _ _) ((N : ℤ) ^ 2) 1 α s s₁ → Φ.Rd 1 s θ → Φ.Rd ((N : ℤ) ^ 2) s₁ (fun z => θ ((N : ℂ) • z)) := by sorry
