-- Prove2me | Theorems.Thm_NSWApxHard_Reduction_completeness
-- name    : NSWApxHard.Reduction.completeness
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:34:36.450924+00:00
-- url     : https://prove2.me/theorems/9e4c65c4-9d10-463e-9235-faa5568cbdd4
-- title:
--   Completeness, p. 2 — a vertex cover of size c_min N gives an allocation with Nash social welfare (1+α)^{β/2.5}
-- statement:
--   Let $G$ be a 3-regular graph on $N$ vertices, let $\alpha\in(1/3,1/2)$, and suppose $G$ has a vertex cover $C$ with $|C|=k$. In the reduced instance with $k$ vertex items there is an allocation $x$ with
--   $$\mathrm{NSW}(x) = (1+\alpha)^{\frac{3k-1.5N}{2.5N}} .$$
--   With $k=c_{\min}N$ and $\beta=3(c_{\min}-0.5)$ the exponent is $\beta N/n=\beta/2.5$, the paper's value $(1+\alpha)^{\beta/2.5}$.
--
--   This is the completeness half of the reduction: a small vertex cover yields high Nash social welfare.
--
--   Differences from the source:
--   - generalization: a vertex cover of size c_min N → a vertex cover of any size k, with k vertex items; reason: the page's computation is valid for every k, and k = c_min N gives (1+α)^{β/2.5}.
--   - encoding: (1+α)^{β/2.5} → (1+α)^{(3k − 1.5N)/(2.5N)}; reason: βN = 3c_min N − 1.5N = 3k − 1.5N and n = 2.5N, the same number.
--   - reading: "the Nash social welfare of the above allocation is (1+α)^{β/2.5}" → some allocation has Nash social welfare exactly (1+α)^{β/2.5}; reason: the explicit allocation is the page's proof, and the claim used on p. 5 is that the reduced instance has this welfare.
--   - encoding: a 3-regular graph with N vertices → a graph on Fin N, N = 0 allowed; reason: for N = 0 there are no agents and both sides equal 1, so no instance of the page changes.
-- source:
--   Lee, APX-Hardness of Maximizing Nash Social Welfare with Indivisible Items, arXiv:1507.01159v1, p. 2, §2, Completeness

import Mathlib
import Definitions.Def_NSWApxHard_Reduction_Instance

namespace NSWApxHard.Reduction

/-- Completeness (Lee, p. 2): if the 3-regular graph `G` has a vertex cover `C` of size `k`, the
reduced instance with `k` vertex items has an allocation of Nash social welfare
`(1 + α)^{(3k - 1.5N)/(2.5N)}`, i.e. `(1 + α)^{β/2.5}` with `β N = 3k - 1.5N`. -/
theorem completeness {N : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj] (k : ℕ) (α : ℝ)
    (hG : IsCubic G) (hα₁ : 1 / 3 < α) (hα₂ : α < 1 / 2)
    (C : Finset (Fin N)) (hC : G.IsVertexCover ↑C) (hCk : C.card = k) :
    ∃ x : Item G k → Agent G,
      nsw (redUtil G k α) x = (1 + α) ^ ((3 * (k : ℝ) - 3 * N / 2) / (5 * N / 2)) := by sorry

end NSWApxHard.Reduction
