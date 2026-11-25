-- Prove2me | Theorems.Thm_GlobalTheory_AdmLoc_admissible_quotient
-- name    : GlobalTheory.AdmLoc.admissible_quotient
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T11:55:30.4369+00:00
-- url     : https://prove2.me/theorems/a1619d98-a7da-58b4-924c-ed9f11ebebe5
-- title:
--   Adm Loc: admissible quotient
-- statement:
--   The Adm Loc construction uses the admissible quotient property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/MkMemAdmissibleAtIffCocycle.lean#L641-L646
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/MkMemAdmissibleAtIffCocycle.lean#L641-L646

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_QuotientHomNonvanishingBound
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_StatementTor
import Definitions.Def_ReciprocityTheory_BasicDefinitions_AdRep
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_PowerSeriesOneAddConstMulXMulInv
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MkMemAdmissibleAtIffCocycle
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.AdmLoc
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions TensorProduct
open Formalism.MainNotions.N (twistRep coefRep)
open Formalism.GaloisCohomology (scalRep)
open ReciprocityTheory.Def (Z1 B1 H1 d0 d1 C1)
open scoped Pointwise
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {n : ℕ} (emb : ZMod n → (K₀ →ₐ[Qp] LL))
variable (Γ : GalData G Qp LL O) (t : ℕ) (Ut : ZMod n → Multiset ℤ)
variable {PD emb Γ t Ut}

theorem GlobalTheory.AdmLoc.admissible_quotient {μ : ℕ} {T : LocLat G Qp LL O} (hT : SumFull PD emb Γ t Ut μ T)
    (L₂ : Lattice (O := O) T.ρ) (hle : L₂.T ≤ T.L.T) [Finite (↥T.L.T ⧸ L₂.T.comap T.L.T.subtype)] :
    Admissible PD emb Γ t Ut
      ((latRep T.L).quotient (L₂.T.comap T.L.T.subtype) (fun g x hx => L₂.stable g x hx)) := by sorry
