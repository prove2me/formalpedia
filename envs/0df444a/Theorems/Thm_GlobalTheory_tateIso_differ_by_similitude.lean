-- Prove2me | Theorems.Thm_GlobalTheory_tateIso_differ_by_similitude
-- name    : GlobalTheory.tateIso_differ_by_similitude
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:59:43.530377+00:00
-- url     : https://prove2.me/theorems/0a43503e-5e82-4d4b-8026-af453fb94581
-- title:
--   Global Theory: tate Iso differ by similitude
-- statement:
--   The Global Theory construction uses the tate Iso differ by similitude property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/TateIsoDifferBySimilitude.lean#L75-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/TateIsoDifferBySimilitude.lean#L75-L115

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_TateIsoDifferBySimilitude
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open scoped CategoryTheory.Obj TensorProduct

theorem GlobalTheory.tateIso_differ_by_similitude :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (k : Type) [Field k] (Q : Type) [Group Q] (act : 𝓞 E → Q → Q) (e : ℕ → Q → Q → kˣ → Prop), (∀ n x y c c', 0 < n → x ^ n = 1 → y ^ n = 1 → e n x y c → e n x y c' → c = c') → ∀ I I' : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.TateIso D k Q act e, ∃ g : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sim D, ∀ n, 0 < n → (∀ a, I'.ev n a = I.ev n (g.f n a)) ∧ I'.ζ n = I.ζ n ^ g.ν n := by sorry
