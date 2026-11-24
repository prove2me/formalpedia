-- Prove2me | Theorems.Thm_GlobalTheory_OrbitScalar_exists_smul_of_orbits
-- name    : GlobalTheory.OrbitScalar.exists_smul_of_orbits
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T18:37:54.502894+00:00
-- url     : https://prove2.me/theorems/b89a4b09-80b1-43bc-aa44-e6855bd9fe0c
-- title:
--   Orbit Scalar: exists smul of orbits
-- statement:
--   The Orbit Scalar construction uses the exists smul of orbits property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/ExistsSmulOfPreservesFrameOrbits.lean#L157-L280
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/ExistsSmulOfPreservesFrameOrbits.lean#L157-L280

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_UnFree
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientDomain
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_ExistsSmulOfPreservesFrameOrbits
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj
open scoped Matrix
open GlobalTheory GlobalTheory.OrbitScalar
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
open NumberField
open scoped Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem GlobalTheory.OrbitScalar.exists_smul_of_orbits : ∀ (E : Type) [Field E] [NumberField E]
    [IsCMField E] (r : ℕ) (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (γ : GL (Fin r) E),
    (∀ x ∈ X.dom, ∃ γ' ∈ X.Γ, ∃ b ∈ _root_.ReciprocityTheory.ChartRestriction.G.FD.Bor X.Ψ r, _root_.ReciprocityTheory.ChartRestriction.G.FD.lact γ x = _root_.ReciprocityTheory.ChartRestriction.G.FD.rmul (_root_.ReciprocityTheory.ChartRestriction.G.FD.lact γ' x) b) →
      ∃ γ' ∈ X.Γ, ∃ u : E, (γ' : Matrix (Fin r) (Fin r) E) = u • (γ : Matrix (Fin r) (Fin r) E) := by sorry
