-- Prove2me | Theorems.Thm_JardenShami_uMap_wellDefined_iff
-- name    : JardenShami.uMap_wellDefined_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:40:41.651195+00:00
-- url     : https://prove2.me/theorems/f1473015-a3ff-4ecf-928a-7673bbb955f2
-- title:
--   Jarden Shami: u Map well Defined iff
-- statement:
--   **Note after Notation 2.5** (Section 2, unnumbered). `u_{a,b}` is well-defined for each
--   `a < b` (i.e. `C(b,c) = C(b,c')` implies `C(a,c) = C(a,c')` for `c, c' > b`) if and only if `C`
--   is locally additive.
--
--   Source: https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section2.lean#L119-L131
-- source:
--   https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section2.lean#L119-L131

import Mathlib.Data.Sym.Sym2
import Mathlib.SetTheory.Cardinal.Regular
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section2
set_option autoImplicit true
open Cardinal
universe v w
noncomputable section
open JardenShami
variable {A : Type w} [LinearOrder A] {D : Type v}

theorem JardenShami.uMap_wellDefined_iff (C : Coloring A D) :
    (∀ (a b c c' : A) (hab : a < b) (hbc : b < c) (hbc' : b < c'),
        C.color b c hbc = C.color b c' hbc' →
          C.color a c (hab.trans hbc) = C.color a c' (hab.trans hbc')) ↔
      IsLocallyAdditive C := by sorry
