-- Prove2me | Theorems.Thm_GaussianPerimeter_VolumeComparison_biSup_add_biSup
-- name    : GaussianPerimeter.VolumeComparison.biSup_add_biSup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T10:14:02.084304+00:00
-- url     : https://prove2.me/theorems/a178d55e-aeed-443e-94ef-9853ce928f4e
-- title:
--   Volume Comparison: bi Sup add bi Sup
-- statement:
--   The Volume Comparison construction uses the bi Sup add bi Sup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/GaussianPerimeter/PrekopaHelpers.lean#L13-L37
-- source:
--   https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/GaussianPerimeter/PrekopaHelpers.lean#L13-L37

module
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Definitions.Def_GaussianPerimeter_PrekopaHelpers
set_option autoImplicit true
@[expose] public section
public section
open GaussianPerimeter GaussianPerimeter.VolumeComparison

theorem GaussianPerimeter.VolumeComparison.biSup_add_biSup
    {ι κ : Sort*}
    {p : ι → Prop} {q : κ → Prop} (hp : ∃ i, p i) (hq : ∃ j, q j)
    {f : ι → ENNReal} {g : κ → ENNReal} :
    (⨆ i, ⨆ _ : p i, f i) + (⨆ j, ⨆ _ : q j, g j) =
    (⨆ i, ⨆ j, ⨆ _ : p i, ⨆ _ : q j, f i + g j) := by sorry
