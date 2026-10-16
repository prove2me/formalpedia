-- Prove2me | Theorems.Thm_NewsBundling_Unilateral_consumer_surplus_eq
-- name    : NewsBundling.Unilateral.consumer_surplus_eq
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T01:06:46.503984+00:00
-- url     : https://prove2.me/theorems/2fcfc3d0-882c-46fc-899f-f2858e0a892f
-- title:
--   Proof of Proposition 1(ii), p. 31 — surplus at equilibrium
-- statement:
--   Let the platform's revenue from news satisfy $0<\phi_0<1$, and consider any cap $0\le\Lambda'<1$. For every subgame-perfect equilibrium $\sigma$ of the game with that cap, consumer surplus, measured by utility at the equilibrium attention allocation, is
--
--   $$CS(\sigma)=1+\frac{(q^*)^2}{2},$$
--
--   where $q^*$ is the equilibrium news quality. This covers both the no-bundling benchmark $\Lambda'=0$ and content bundling $\Lambda'=\Lambda$, and makes surplus strictly increasing in quality for positive qualities.
--
--   **Formalization Note** Surplus is defined from consumer utility at the equilibrium outcome. The formula is a theorem, not the definition of surplus.
-- source:
--   de Cornière & Sarvary, Social Media and News: Content Bundling and News Quality, TSE Working Paper n° 1152 (August 2021), App. A, p. 31, proof of Proposition 1(ii), final sentence; p. 15, proof of Proposition 3(1)

import Mathlib
import Definitions.Def_NewsBundling_Unilateral_Setting

namespace NewsBundling.Unilateral

/-- Proof of Proposition 1(ii), p. 31: surplus at either game's equilibrium. -/
theorem consumer_surplus_eq (β φ0 φ1 c : ℝ)
    (hφ0 : 0 < φ0 ∧ φ0 < 1) :
    ∀ Λ' : ℝ, 0 ≤ Λ' → Λ' < 1 →
      ∀ σ, IsSPE β φ0 φ1 c Λ' σ →
        consumerSurplus σ = 1 + σ.quality ^ 2 / 2 := by sorry

end NewsBundling.Unilateral
