-- Prove2me | Theorems.Thm_HopRamsey_remove_finite_diameter
-- name    : HopRamsey.remove_finite_diameter
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T21:47:02.987837+00:00
-- url     : https://prove2.me/theorems/59c6b323-1e76-46a5-9356-35deff0d92a4
-- title:
--   §4.4: removing the assumption $\mathrm{diam}^{(h)}_G(V)<\infty$
-- statement:
--   Let $G$ be a weighted graph on a finite vertex set $V$, $h$ a hop parameter, $\Phi'$ the largest finite $h$-hop distance of $G$, and let $\rho\ge1$, $\eta\in\mathbb N$, $\varepsilon,\alpha$ be parameters and $\omega>0$ with $2\rho\Phi'\le\omega$. Let $G'$ be $G$ plus an edge of weight $\omega$ between every pair of distinct non-adjacent vertices. Suppose $\mathcal D'$ is a distribution over pairs (HST on $V$, saved set) that, with respect to $G'$ and $h$, has hop-stretch $\eta$, distortion $\rho$, exclusion probability $\varepsilon$ and expected distortion $\alpha$. Replace in every HST each label $l>\omega/2$ by $\infty$ and keep the saved set. Then the resulting distribution is over HSTs on $V$ and, with respect to the original $G$ and $h$, has the same four parameters: hop-stretch $\eta$, distortion $\rho$, exclusion probability $\varepsilon$ and expected distortion $\alpha$.
--
--   Since $G'$ has finite $h$-hop diameter, this reduces Theorem 1 to the finite case.
--
--   Differences from the source:
--   - generalization: ω = 2ρ·Φ′ → any ω > 0 with 2ρ·Φ′ ≤ ω; reason: the argument uses only ω ≥ 2ρΦ′ (and ω > 0 to be an edge weight); this also covers Φ′ = 0, where 2ρΦ′ = 0 is not a positive weight
--   - generalization: ρ, η the distortion and hop-stretch ε^{−1}·Õ(log n) of the finite case, and expected distortion Õ(log n) → any η ∈ ℕ, any ρ ≥ 1, any ε and α; reason: the transfer argument does not use the values; ρ ≥ 1 holds for the paper's ρ = ε^{−1}·Õ(log n)
--   - reading: "the distribution over the resulting HST satisfies Theorem 1 w.r.t. the original G" (bullets on pp.25–26) → the image law has hop-stretch η, distortion ρ, exclusion ε and expected distortion α for G and h, and all its HSTs have leaf set V; reason: these are the four bullets
--   - encoding: HSTs U′, U and the replacement of labels > ω/2 by ∞ → `truncateLabels` on the leaf ultrametric, with leaf set V on the support; reason: the statements read only the leaf distances
--   - encoding: d^{(h)}_G as a minimum over paths with at most h hops → infimum over walks with at most h edges, in [0,∞]; reason: positive weights: removing a cycle lowers both weight and hop count, so both values agree; ∞ when no such walk exists
-- source:
--   Filtser, Zuzic, Trees with Benefits: Stochastic Hop-Constrained Ramsey-Type Embeddings with Logarithmic Expected Distortion, STOC 2027 submission (manuscript sha256 1ee73385…), §4.4, pp.25–26 (PDF pp.27–28)

import Mathlib
import Definitions.Def_ARTreeCover_WGraph
import Definitions.Def_ARTreeCover_HST
import Definitions.Def_HopRamsey_hopDist
import Definitions.Def_HopRamsey_IsStochRamseyEmbedding
import Definitions.Def_HopRamsey_augmentComplete
import Definitions.Def_HopRamsey_truncateLabels

open scoped ENNReal

namespace HopRamsey

open ARTreeCover

/-- Filtser, Zuzic, *Trees with Benefits: Stochastic Hop-Constrained Ramsey-Type Embeddings with
Logarithmic Expected Distortion*, STOC 2027 submission (manuscript sha256 1ee73385…),
§4.4 reduction, pp.25–26 (PDF pp.27–28): "We create an auxiliary graph G′ by taking G and adding an
edge of weight ω = 2ρ·Φ′ between every pair of non-adjacent vertices. [...] Finally, we create a
new HST U from U′ by replacing each label l such that l > ρ·Φ′ = ω/2 by ∞. M̂ remains the saved set
also for U. We argue that the distribution over the resulting HST satisfies Theorem 1 w.r.t. the
original G" (followed by the bullets "Save probability", "Hop-stretch", "Distortion", "Expected
distortion", pp.25–26).

**Formalization Note.** `Φ′ = maxFiniteHopDist G h`. The weight `ω` is any `ω > 0` with
`2ρ·Φ′ ≤ ω` (the paper takes `ω = 2ρΦ′`; `ω > 0` is needed for a weight, and also covers
`Φ′ = 0`). `ρ ≥ 1` is the distortion and `η` the hop-stretch of the law `D′` for `G′`, with
exclusion `ε` and expected distortion `α`; the conclusion is that the image law, with labels above
`ω/2` replaced by `∞` and the same saved sets, has the same four parameters for `G`, on HSTs with
leaf set `V`. -/
theorem remove_finite_diameter {V : Type} [Fintype V] [DecidableEq V] (G : WGraph V) (h η : ℕ)
    (ρ ε α ω : ℝ) (hρ : 1 ≤ ρ) (hω : 0 < ω)
    (hωΦ : ENNReal.ofReal (2 * ρ) * maxFiniteHopDist G h ≤ ENNReal.ofReal ω)
    (D' : PMF (HST V × Finset V)) (hleaves : ∀ x ∈ D'.support, x.1.leaves = Set.univ)
    (hD' : IsStochRamseyEmbedding (augmentComplete G ω hω) h D' η ρ ε α) :
    (∀ x ∈ (D'.map fun x => (truncateLabels x.1 (ENNReal.ofReal (ω / 2)), x.2)).support,
        x.1.leaves = Set.univ) ∧
      IsStochRamseyEmbedding G h (D'.map fun x => (truncateLabels x.1 (ENNReal.ofReal (ω / 2)), x.2))
        η ρ ε α := by sorry

end HopRamsey
