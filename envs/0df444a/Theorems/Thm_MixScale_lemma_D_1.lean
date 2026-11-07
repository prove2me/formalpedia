-- Prove2me | Theorems.Thm_MixScale_lemma_D_1
-- name    : MixScale.lemma_D_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:11:53.654205+00:00
-- url     : https://prove2.me/theorems/9a85451d-8c11-4603-8e58-0014b7dc58be
-- title:
--   Lemma D.1, p.25 — one joint geometric event
-- statement:
--   Let $\Theta$ satisfy (2), with directions as in (43). The event $G$ on which
--
--   1. $|u^\top(\mu_j-\mu_\ell)|\ge4\Delta_A$ for every $j\ne\ell$,
--   2. $|p^\top(\mu_j-\mu_\ell)|\ge4\Delta_T$ for every stable $p$ and $j\ne\ell$,
--   3. $\|z\|\le1/(100d^{3/2})$,
--
--   depends only on the directions and the centers, and has probability at least $0.96$. On $G$, all anchor and stable directions have norm in $[1/2,2]$, and the scalar conditions (17) hold with $M=2B$, $K=4\kappa$, with separation $\Delta_A$ for anchors and $\Delta_T$ for stable directions.
--
--   This one event justifies both the matching of components across directions and the matrix reconstruction.
--
--   Differences from the source:
--   - generalization: There is an event G of probability at least 0.96 → the explicit set of (g, g′) where clauses 1–3 hold is measurable and has probability at least 0.96; reason: this is the proof's event and it implies the existence claim
--   - encoding: all scalar conditions hold with M = 2B and K = 4κ → Scalar17 for each direction, with b_j = p⊤μ_j, v_j = p⊤Σ_j p, w_j as given; reason: (17) and the definitions of p.14
--   - encoding: the bounds of (2) → 1 ≤ B, 1 ≤ κ, 0 < γ ≤ 1, 0 < d, 0 < k; reason: standing assumptions of p.2
-- source:
--   Wang–Zhang, Learning Mixtures with Unknown Scales: Sharp Dependence on Separation, STOC 2027 submission (sha256 5277f95e…), Lemma D.1, p.25 (PDF p.27); (43), p.25

import Mathlib
import Definitions.Def_MixScale_Directions
import Definitions.Def_MixScale_Scalar

open MeasureTheory

namespace MixScale

/-- **Lemma D.1** (One joint geometric event).

S. Wang and X. Zhang, *Learning Mixtures with Unknown Scales: Sharp Dependence on Separation*, STOC
2027 submission manuscript (sha256 5277f95e…7c6c), Lemma D.1, p.25 (PDF p.27), with (43).

`G = GeoEvent γ (center Θ)`, the explicit event of clauses 1–3. It is measurable and has probability
at least `0.96` under `g, g′ ∼ N(0, I_d)` independent. On `G`, all directions have norm in `[1/2, 2]`
and the scalar conditions (17) hold with `M = 2B`, `K = 4κ`, separation `Δ_A` for anchors and `Δ_T` for
stable directions.

**Formalization Note.** "There is an event `G`" is stated for the explicit set where clauses 1–3
hold, which is the proof's event and is stronger than `∃ G`. `1 ≤ B`, `1 ≤ κ`, `0 < γ ≤ 1` are the
standing bounds of (2). The scalar center and scale in direction `p` are `p⊤μ_j`, `p⊤Σ_j p` (p.14). -/
theorem lemma_D_1 {d k : ℕ} (hd : 0 < d) (hk : 0 < k) (B κ wstar γ : ℝ) (hB : 1 ≤ B) (hκ : 1 ≤ κ)
    (hγ₀ : 0 < γ) (hγ₁ : γ ≤ 1) (Θ : Params d k) (hΘ : Valid B κ wstar γ Θ) :
    MeasurableSet (GeoEvent γ (center Θ)) ∧
    ENNReal.ofReal 0.96 ≤ ((stdGaussian d).prod (stdGaussian d)) (GeoEvent γ (center Θ)) ∧
    ∀ x ∈ GeoEvent γ (center Θ),
      (∀ i : Option (Fin d),
        1 / 2 ≤ ‖anchorDir γ B k x.1 i‖ ∧ ‖anchorDir γ B k x.1 i‖ ≤ 2 ∧
        Scalar17 (2 * B) (4 * κ) (DeltaA γ k d) wstar
          (fun j => inner ℝ (anchorDir γ B k x.1 i) (center Θ j))
          (fun j => quadForm (scale Θ j) (anchorDir γ B k x.1 i)) (weight Θ)) ∧
      (∀ p : StableIdx d,
        1 / 2 ≤ ‖stableDir (pertZ x.2) p‖ ∧ ‖stableDir (pertZ x.2) p‖ ≤ 2 ∧
        Scalar17 (2 * B) (4 * κ) (DeltaT γ k d) wstar
          (fun j => inner ℝ (stableDir (pertZ x.2) p) (center Θ j))
          (fun j => quadForm (scale Θ j) (stableDir (pertZ x.2) p)) (weight Θ)) := by sorry

end MixScale
