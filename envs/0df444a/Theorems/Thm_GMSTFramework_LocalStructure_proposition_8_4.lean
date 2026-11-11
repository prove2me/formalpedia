-- Prove2me | Theorems.Thm_GMSTFramework_LocalStructure_proposition_8_4
-- name    : GMSTFramework.LocalStructure.proposition_8_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T19:02:18.405718+00:00
-- url     : https://prove2.me/theorems/c19479a9-5499-4164-ad66-d6db97b897c0
-- title:
--   Proposition 8.4 — graphs embeddable in $\Sigma(h,c)$ are minors of the extended $c_{8.4}g^4(|V(H)|+g)^2$-surface-wall; controlled complete models; $K_t$ from $2h+c=t^2$, $k\in\Omega(t^{12})$ [GSW25b]
-- statement:
--   (Cited from [GSW25b] as printed in this paper.) There is a universal constant $c_{8.4}$ such that for all $c,h,t\ge0$ every graph $H$ that embeds in a surface homeomorphic to the sphere with $h$ handles and $c$ crosscaps is a minor of the extended $c_{8.4}g^4(|V(H)|+g)^2$-surface-wall $W$ with $h$ handles, $c$ crosscaps, 0 flaps and 0 vortices, $g=2h+c$; if $H$ is complete there is an $H$-minor-model controlled by $W$. In particular $K_t$ is a minor of every extended $k$-surface-wall with $h$ handles and $c$ crosscaps where $2h+c=t^2$ and $k\in\Omega(t^{12})$.
--
--   Differences from the source:
--   - reading: "the extended N-surface-wall W" (a subdivision, segments in some cyclic order) → every graph G spanned by an extended N-surface-wall D (D.sub = ⊤) with signature (h, c, 0, 0); reason: the claim is meant for every such wall; "the" names the type of object
--   - encoding: a surface homeomorphic to the sphere with h handles and c crosscaps → SigmaHC h c (fundamental polygon); reason: embeddability is invariant under homeomorphism
--   - encoding: universal constant c8.4; k ∈ Ω(t¹²) → c84 ∈ ℕ with c84 ≥ 1; ∃ c₀ ≥ 1 with every k ≥ c₀·t¹²; reason: wall orders are integers; a positive real constant can be rounded up; c84 = 0 would make every wall order 0 and the first clause vacuous
--   - encoding: "H complete"; "controlled by W" → ∀ u ≠ v, H.Adj u v; controlled by the tangle D.tangle of the wall; reason: control by a wall is control by its tangle (p. 24)
--   - encoding: extended n-surface-walls, defined for n ≥ 2 (p. 21) → SurfaceWall requires 2 ≤ n; reason: as defined; for g = 0 the order c8.4·g⁴(…)² is 0, no such wall exists, and the first clause is vacuous there
-- source:
--   Gorsky, Protopapas, Wiederrecht, A unifying framework for Graph Minor Structure Theorems with polynomial bounds, STOC 2027 submission (manuscript sha256 b2ee466d…), Proposition 8.4, p. 86 (PDF 89)

import Mathlib
import Definitions.Def_GMSTFramework_LocalStructure_Surfaces
import Definitions.Def_GMSTFramework_LocalStructure_SurfaceWalls

open scoped Classical

namespace GMSTFramework.LocalStructure

/-- Proposition 8.4 ([GSW25b]): every graph embeddable in `Σ(h,c)` is a minor of the extended
`c₈.₄ g⁴(|V(H)| + g)²`-surface-wall with `h` handles and `c` crosscaps (`g = 2h + c`), complete graphs
with a controlled model; in particular `K_t` is a minor of every extended `k`-surface-wall with
`2h + c = t²` and `k ∈ Ω(t¹²)`. "The surface-wall `W`" is every graph `G` that is (spanned by) such
a wall `D`. -/
theorem proposition_8_4 :
    (∃ c84 : ℕ, 1 ≤ c84 ∧ ∀ c h t : ℕ,
      ∀ {W : Type} [Fintype W] (H : SimpleGraph W), EmbedsIn H (SigmaHC h c) →
      ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
        (D : SurfaceWall G (c84 * (2 * h + c) ^ 4 * (Fintype.card W + (2 * h + c)) ^ 2)),
        D.HasSignature h c 0 0 → D.sub = ⊤ →
          Nonempty (H.Minor G) ∧
          ((∀ u v, u ≠ v → H.Adj u v) → ∃ μ : H.Minor G, ControlledBy μ D.tangle)) ∧
    (∃ c₀ : ℕ, 1 ≤ c₀ ∧ ∀ t h c k : ℕ, 2 * h + c = t ^ 2 → c₀ * t ^ 12 ≤ k →
      ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (D : SurfaceWall G k),
        D.HasSignature h c 0 0 → D.sub = ⊤ →
          Nonempty ((SimpleGraph.completeGraph (Fin t)).Minor G)) := by sorry

end GMSTFramework.LocalStructure
