-- Prove2me | Theorems.Thm_GlobalTheory_ProjSpace_isClosedImmersion_sigmaDesc
-- name    : GlobalTheory.ProjSpace.isClosedImmersion_sigmaDesc
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:16:15.822851+00:00
-- url     : https://prove2.me/theorems/088671c4-25cf-5b23-923a-fa16fb2ef3cb
-- title:
--   Proj Space: is Closed Immersion sigma Desc
-- statement:
--   The Proj Space construction uses the is Closed Immersion sigma Desc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/IsClosedImmersionSigmaDesc.lean#L31-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/IsClosedImmersionSigmaDesc.lean#L31-L52

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_IsClosedImmersionIffPullRatio
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_IsClosedImmersionSigmaDesc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap PSpace resG IsProjOver)
open GlobalTheory GlobalTheory.ProjSpace
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace MvPolynomial

theorem GlobalTheory.ProjSpace.isClosedImmersion_sigmaDesc {ι : Type} [Finite ι]
    {X : ι → Scheme.{0}} {Y : Scheme.{0}}
    (f : ∀ i, X i ⟶ Y) (hf : ∀ i, IsClosedImmersion (f i))
    (h : Pairwise fun i j => Disjoint (Set.range (f i)) (Set.range (f j))) :
    IsClosedImmersion (Sigma.desc f) := by sorry
