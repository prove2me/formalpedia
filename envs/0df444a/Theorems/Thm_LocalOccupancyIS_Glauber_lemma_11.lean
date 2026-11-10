-- Prove2me | Theorems.Thm_LocalOccupancyIS_Glauber_lemma_11
-- name    : LocalOccupancyIS.Glauber.lemma_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T10:58:52.478463+00:00
-- url     : https://prove2.me/theorems/9b09e91e-3844-494c-a0bd-beccfee958e9
-- title:
--   Lemma 11 — average occupancy after two and three sweeps
-- statement:
--   Let $t\ge1$ be an integer, $b\ge0$, and let $F$ be a finite simple graph on $k\ge1$ vertices satisfying $2tN_t(F)\le bk$. Set $s=(b+1)^{1/(2t-1)}$. Starting from any independent set, perform three full heat-bath sweeps at fugacity $\lambda>0$, each in a deterministic order; the orders may differ. Let $X$ and $Y$ be the sets after the second and third sweeps, and write $p=\lambda/(1+\lambda)$. Then
--
--   $$\frac{\mathbb E|X|+\mathbb E|Y|}{2}\ge\frac{pk(1-8tsp)}{2(1+4tps^{1/t}k^{1-1/t})}.$$
--
--   No positivity condition is added to $1-8tsp$. This is the large-available-graph endpoint estimate for the three-sweep certificate.
--
--   Differences from the source:
--   - encoding: finite independent sets and induced subgraphs → Boolean configurations on finite types and induced subtypes; reason: these presentations preserve all feasible configurations, including the empty one
-- source:
--   Ewan Davies, Brian Tan, STOC 2027 submission #982 (October 2026), Lemma 11, p. 18; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/982.pdf#page=18

import Definitions.Def_LocalOccupancyIS_Glauber_Parameters

namespace LocalOccupancyIS.Glauber
/-- Lemma 11, p.18, including the regime of a negative right hand side. -/
theorem lemma_11 {V : Type} [Fintype V] [DecidableEq V]
    (F : SimpleGraph V) [DecidableRel F.Adj] (t : ℕ) (ht : 1 ≤ t)
    (b lam : ℝ) (hb : 0 ≤ b) (hlam : 0 < lam)
    (hk : 1 ≤ Fintype.card V) (hd : Density F t b)
    (w₁ w₂ w₃ : List V) (h₁ : IsSweep Finset.univ w₁)
    (h₂ : IsSweep Finset.univ w₂) (h₃ : IsSweep Finset.univ w₃) (I : State F) :
    let X := push (point I) (word F lam (w₁ ++ w₂))
    let Y := push (point I) (word F lam (w₁ ++ w₂ ++ w₃))
    (expectation X (fun σ => size σ.val) + expectation Y (fun σ => size σ.val)) / 2 ≥
      p lam * Fintype.card V * (1 - 8*t*scale t b*p lam) /
        (2*(1+4*t*p lam*(scale t b)^(1/(t:ℝ))*(Fintype.card V : ℝ)^(1-1/(t:ℝ)))) := by sorry
end LocalOccupancyIS.Glauber
