-- Prove2me | Theorems.Thm_MainStatements_Hodge_Pf_WedgeProjections_key_alg
-- name    : MainStatements.Hodge.Pf.WedgeProjections.key_alg
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T13:03:30.368285+00:00
-- url     : https://prove2.me/theorems/a3d120d4-61aa-5d8d-9d70-eed6eb43e9cd
-- title:
--   Wedge Projections: key alg
-- statement:
--   The Wedge Projections construction uses the key alg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/AbelianDeRham/AbelianWedgeProducts/ThetaMulti.lean#L24-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/AbelianDeRham/AbelianWedgeProducts/ThetaMulti.lean#L24-L61

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_AbelianDeRham_AbelianWedgeProducts_ThetaMulti
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
open MainStatements MainStatements.Hodge MainStatements.Hodge.Pf MainStatements.Hodge.Pf.WedgeProjections

theorem MainStatements.Hodge.Pf.WedgeProjections.key_alg {K : Type} [Field K] {V W : Type} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (p q : V →ₗ[K] W) (r₁ r₂ : W →ₗ[K] V) (h11 : r₁ ∘ₗ p = LinearMap.id) (h12 : r₁ ∘ₗ q = 0)
    (h21 : r₂ ∘ₗ p = 0) (h22 : r₂ ∘ₗ q = LinearMap.id) (t : ⋀[K]^2 V)
    (ht : exteriorPower.map 2 (p + q) t = exteriorPower.map 2 p t + exteriorPower.map 2 q t) : t = 0 := by sorry
