-- Prove2me | Theorems.Thm_GroundTheory_Global_cycTateZeroOrbitEquiv_mk
-- name    : GroundTheory.Global.cycTateZeroOrbitEquiv_mk
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:56:18.572835+00:00
-- url     : https://prove2.me/theorems/57e37f4e-6863-4549-b8bc-ad6aba140ffb
-- title:
--   Global: cyc Tate Zero Orbit Equiv mk
-- statement:
--   The Global construction uses the cyc Tate Zero Orbit Equiv mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/HerbrandQuotients/CycTateNegOneOrbitEquivSymmMk.lean#L268-L276
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/HerbrandQuotients/CycTateNegOneOrbitEquivSymmMk.lean#L268-L276

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_HerbrandAbstract
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_CycTate
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_CycTateNegOneOrbitEquivSymmMk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open GroundTheory.GroupCoh
variable {k G X : Type*} [CommRing k] [Group G] [MulAction G X]
  {M : X → Type*} [∀ x, AddCommGroup (M x)] [∀ x, Module k (M x)]
variable [MulAction.IsPretransitive G X]

theorem GroundTheory.Global.cycTateZeroOrbitEquiv_mk [Fintype G] (ρ : Representation k G (∀ x, M x))
    (hρ : PermutesFactors ρ) (x₀ : X) (D : Subgroup G) [Fintype D]
    (hD : ∀ g, g ∈ D ↔ g • x₀ = x₀) (ρ₀ : Representation k D (M x₀))
    (hρ₀ : ∀ (d : D) (f : ∀ x, M x), ρ d f x₀ = ρ₀ d (f x₀)) (σ : G)
    (hσ : ∀ g, g ∈ Subgroup.zpowers σ) (τ : D) (hτ : ∀ d, d ∈ Subgroup.zpowers τ)
    (f : (cycSubOne ρ σ).ker) :
    cycTateZeroOrbitEquiv ρ hρ x₀ D hD ρ₀ hρ₀ σ hσ τ hτ (QuotientAddGroup.mk f) =
      QuotientAddGroup.mk ⟨(f : ∀ x, M x) x₀, base_mem_ker_cycSubOne hρ₀ hσ τ f⟩ := by sorry
