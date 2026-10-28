-- Prove2me | Theorems.Thm_NSWApxHard_Reduction_lemma_2_4
-- name    : NSWApxHard.Reduction.lemma_2_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:34:39.588978+00:00
-- url     : https://prove2.me/theorems/5502cdbe-9e55-4f07-afcd-9b8f7626a33b
-- title:
--   Lemma 2.4 — if every vertex cover has ≥ c_max N vertices, the optimal NSW is at most (2(1+α)/3)^{γ/2.5}(1+α)^{β/2.5}
-- statement:
--   Let $G$ be a 3-regular graph on $N$ vertices, let $\alpha\in(1/3,1/2)$, and consider the reduced instance with $k<N$ vertex items. Let $K'$ be a real number such that every vertex cover of $G$ has at least $K'$ vertices. Then every allocation $x$ satisfies
--   $$\mathrm{NSW}(x)\le\Big(\frac{2(1+\alpha)}{3}\Big)^{\frac{(K'-k)/3}{2.5N}}\,(1+\alpha)^{\frac{3k-1.5N}{2.5N}} .$$
--   With $k=c_{\min}N$, $K'=c_{\max}N$, $\gamma=(c_{\max}-c_{\min})/3$ and $\beta=3(c_{\min}-0.5)$ the right-hand side is the paper's $\big(\tfrac{2(1+\alpha)}{3}\big)^{\gamma/2.5}(1+\alpha)^{\beta/2.5}$.
--
--   This is the soundness half of the reduction. Since $\frac{2(1+\alpha)}{3}<1$ for $\alpha<1/2$, the bound is a constant factor below the completeness value $(1+\alpha)^{\beta/2.5}$ whenever $K'>k$.
--
--   Differences from the source:
--   - generalization: c_min N vertex items and covers of size at least c_max N → any number k < N of vertex items and any real lower bound K′ on the size of every vertex cover; reason: k = c_min N, K′ = c_max N give the page's statement.
--   - generalization: "for some universal constant γ > 0" → the explicit γN = (K′ − k)/3; reason: this is the γ := (c_max − c_min)/3 fixed in the proof (p. 5); it is positive when K′ > k, so the statement implies the page's existential one.
--   - encoding: "the optimal Nash social welfare is at most" → every allocation has Nash social welfare at most the bound; reason: there are finitely many allocations, so the optimum is attained and both say the same.
--   - encoding: (2(1+α)/3)^{γ/2.5}(1+α)^{β/2.5} → exponents ((K′ − k)/3)/(2.5N) and (3k − 1.5N)/(2.5N); reason: γN = (c_max − c_min)N/3, βN = 3k − 1.5N and n = 2.5N, the same numbers.
--   - reading: the section's standing assumptions (G 3-regular, "Let α be a constant in (1/3, 1/2)", p. 2) and c_min N < N (p. 3) → explicit hypotheses; reason: Lemma 2.4's sentence does not repeat them.
-- source:
--   Lee, APX-Hardness of Maximizing Nash Social Welfare with Indivisible Items, arXiv:1507.01159v1, p. 4, Lemma 2.4 (proof pp. 4–5, γ := (c_max − c_min)/3 on p. 5)

import Mathlib
import Definitions.Def_NSWApxHard_Reduction_Instance

namespace NSWApxHard.Reduction

/-- Lemma 2.4 (Lee, p. 4): if every vertex cover of the 3-regular graph `G` has at least `K'`
vertices (the paper's `c_max N`) and there are `k < N` vertex items (the paper's `c_min N`), then
every allocation of the reduced instance has Nash social welfare at most
`(2(1+α)/3)^{γ/2.5} (1 + α)^{β/2.5}`, where `γ N = (K' - k)/3` and `β N = 3k - 1.5N`. -/
theorem lemma_2_4 {N : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj] (k : ℕ) (α K' : ℝ)
    (hG : IsCubic G) (hα₁ : 1 / 3 < α) (hα₂ : α < 1 / 2) (hk : k < N)
    (hK' : ∀ C : Finset (Fin N), G.IsVertexCover ↑C → K' ≤ (C.card : ℝ))
    (x : Item G k → Agent G) :
    nsw (redUtil G k α) x ≤
      (2 * (1 + α) / 3) ^ (((K' - k) / 3) / (5 * N / 2)) *
        (1 + α) ^ ((3 * (k : ℝ) - 3 * N / 2) / (5 * N / 2)) := by sorry

end NSWApxHard.Reduction
