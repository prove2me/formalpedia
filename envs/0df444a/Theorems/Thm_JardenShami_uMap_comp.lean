-- Prove2me | Theorems.Thm_JardenShami_uMap_comp
-- name    : JardenShami.uMap_comp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:40:43.123434+00:00
-- url     : https://prove2.me/theorems/fdda091f-0f14-4290-b4f0-3324689bd134
-- title:
--   Jarden Shami: u Map comp
-- statement:
--   **Claim 2.8** (Section 2, `\label{C^* is additive}`). For a locally additive `C` and
--   `a < b < c`: `u_{a,b} ∘ u_{b,c} = u_{a,c}` as functions on `D_c`. The composition makes sense
--   because `u_{b,c}` maps `D_c` into `D_b`; this is part of the statement.
--
--   Source: https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section2.lean#L145-L152
-- source:
--   https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section2.lean#L145-L152

import Mathlib.Data.Sym.Sym2
import Mathlib.SetTheory.Cardinal.Regular
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section2
set_option autoImplicit true
open Cardinal
universe v w
noncomputable section
open JardenShami
variable {A : Type w} [LinearOrder A] {D : Type v}

theorem JardenShami.uMap_comp {C : Coloring A D} (hC : IsLocallyAdditive C) {a b c : A}
    (hab : a < b) (hbc : b < c) :
    ∀ t : Dset C c, ∃ h : uMap C b c hbc t ∈ Dset C b,
      uMap C a b hab ⟨uMap C b c hbc t, h⟩ = uMap C a c (hab.trans hbc) t := by sorry
