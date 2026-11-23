-- Prove2me | Theorems.Thm_NoHair_asymptoticallyFlatEnd_timelike_restriction
-- name    : NoHair.asymptoticallyFlatEnd_timelike_restriction
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-23T06:58:09.322799+00:00
-- url     : https://prove2.me/theorems/0121e09f-d259-4579-a172-1c86b67aebe2
-- title:
--   A stationary asymptotically flat end restricts to a timelike end
-- statement:
--   Let a stationary asymptotically flat chart have radius $R_0$ and metric falloff constant $C$. For every $R\ge\max(R_0,C)$, restricting the same chart to $|x|>R$ gives an asymptotically flat end with the same decay constant. The stationary flow generator is timelike everywhere in its image. This quantifies the choice of the timelike reference end used when defining the domain of outer communications.
-- source:
--   P. T. Chruściel, The classification of static vacuum space-times containing an asymptotically flat spacelike hypersurface with compact interior, Class. Quantum Grav. 16 (1999) 661–687, section 2, equations (2.2)–(2.4), https://homepage.univie.ac.at/piotr.chrusciel/papers/chrusciel/static.pdf.

import Definitions.Def_NoHair_spacetime

open NoHair Set
open scoped ContDiff Manifold

theorem NoHair.asymptoticallyFlatEnd_timelike_restriction {M : Type*} [TopologicalSpace M]
    [ChartedSpace E4 M] [IsManifold 𝓘(ℝ, E4) ∞ M] (g F : BilinField M)
    (φ : ℝ → M → M) (E : AsymptoticallyFlatEnd g F φ) (R : ℝ) (hR : E.R ≤ R) (hC : E.C ≤ R) :
    ∃ E' : AsymptoticallyFlatEnd g F φ,
      E'.R = R ∧ E'.ψ = E.ψ ∧ E'.C = E.C ∧ E'.region = E.ψ '' exteriorRegion R ∧
      ∀ x ∈ E'.region, g x (flowGenerator φ x) (flowGenerator φ x) < 0 := by sorry
