-- Prove2me | Theorems.Thm_JardenShami_isStarLocallyAdditive_iff
-- name    : JardenShami.isStarLocallyAdditive_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:43:14.381893+00:00
-- url     : https://prove2.me/theorems/1e9f9092-7413-468f-9dc2-f7ed58465767
-- title:
--   Jarden Shami: is Star Locally Additive iff
-- statement:
--   AUX: not in paper. *-local additivity spelled out in the original order: for
--   `x < y < z < w`, `C(y,z) = C(x,z)` implies `C(y,w) = C(x,w)`.
--
--   Source: https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section7.lean#L62-L80
-- source:
--   https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section7.lean#L62-L80

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section6
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section7
set_option autoImplicit true
open Cardinal
universe v w
noncomputable section
open JardenShami
open Tree

theorem JardenShami.isStarLocallyAdditive_iff {A : Type w} [LinearOrder A] {D : Type v} (C : Coloring A D) :
    IsStarLocallyAdditive C ↔
      ∀ (x y z w : A) (hxy : x < y) (hyz : y < z) (hzw : z < w),
        C.color y z hyz = C.color x z (hxy.trans hyz) →
          C.color y w (hyz.trans hzw) = C.color x w ((hxy.trans hyz).trans hzw) := by sorry
