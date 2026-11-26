-- Prove2me | Theorems.Thm_LocalLemma_CoordDep_measurableSet
-- name    : LocalLemma.CoordDep.measurableSet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:20:19.30981+00:00
-- url     : https://prove2.me/theorems/05420443-5aec-5c6f-9037-6fc9e218df3d
-- title:
--   Coord Dep: measurable Set
-- statement:
--   The Coord Dep construction uses the measurable Set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/lovasz-local-lemma/blob/9d020fa8fb20e9426c2d6780a3cfab4a68794d89/LocalLemmaLib/Coin.lean#L38-L48
-- source:
--   https://github.com/jtraverso/lovasz-local-lemma/blob/9d020fa8fb20e9426c2d6780a3cfab4a68794d89/LocalLemmaLib/Coin.lean#L38-L48

module
public import Mathlib
public import Definitions.Def_LocalLemmaLib_Coin
set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory ProbabilityTheory
open LocalLemma

theorem LocalLemma.CoordDep.measurableSet {ι : Type*} {A : Set (ι → Bool)} {D : Finset ι}
    (h : CoordDep A D) :
    MeasurableSet[MeasurableSpace.comap (fun ω (i : D) => ω i) MeasurableSpace.pi] A := by sorry
