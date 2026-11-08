-- Prove2me | Theorems.Thm_HardcoreSlices_sampling_cases
-- name    : HardcoreSlices.sampling_cases
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:41:06.835211+00:00
-- url     : https://prove2.me/theorems/e017cf82-467e-4a73-b1ba-8c232b8a215b
-- title:
--   Approximate sampling, Cases 1–3 — a round returns $I$ with probability $\lambda^{|I|}/(4\hat Z_G)$
-- statement:
--   Let $G$ be bipartite with sides of size $m$, $\lambda>0$, and $\alpha,\beta$ real. Let $\hat Z_j>0$ on the low and medium labels, and let the proposal functions be positive on link vertices. Suppose every acceptance ratio of Cases 1 and 2 is at most $1$. Then one round of the sampler of §6 returns a set $I$ with probability
--   $$\begin{cases}\dfrac{\lambda^{|I|}}{4\hat Z_G(\lambda)}&\text{if $I$ is independent,}\\[1ex]0&\text{otherwise.}\end{cases}$$
--   So conditioned on returning a set, the round returns an exact sample from $\mu_\lambda$, and the probability that it returns anything is $Z_G(\lambda)/(4\hat Z_G(\lambda))$. If moreover $\beta=4\lambda$, then
--   $$Z_X(\lambda)\le(1+\lambda)^{|Y|}\le Z_G(\lambda).$$
--   This is the correctness of the sampler; the estimates enter only through the hypotheses on the ratios.
--
--   Differences from the source:
--   - generalization: qτ(v) = (π̂τ(v) + η)/(1 + |Xτ(1)|η), and Ẑj FPRAS outputs → any positive proposal function and any positive Ẑj with every ratio at most 1; reason: the identity uses nothing else; the source is the case of its q and Ẑj, where p.31 shows the ratios are at most 1
--   - encoding: accept with probability r → accept with probability min{1, r}; reason: r ≤ 1 is a hypothesis, so they agree
--   - reading: low, medium and high with the ends of p.26 → k ≤ αm; αm < k ≤ βm; k > max(α, β)m; reason: these match Z̃, and they partition ℕ
-- source:
--   Kocurek, Oveis Gharan, Tjowasi, Sampling from the Hardcore Model on Random Regular Bipartite Graphs above the Uniqueness Threshold, arXiv:2604.21847 (version held, sha256 363c225d…), §6, Approximate sampling, Cases 1–3, pp.29–33

import Mathlib
import Definitions.Def_HardcoreSlices_roundProb

open Classical

namespace HardcoreSlices

open ExpanderBIS.RandomHardCore

/-- **Approximate sampling, Cases 1–3.** Kocurek, Oveis Gharan, Tjowasi, *Sampling from the Hardcore Model on Random Regular Bipartite Graphs above the Uniqueness Threshold*, arXiv:2604.21847 (version held, sha256 363c225d…), §6, pp.29–33: "`Pr[I sampled] = λ^|I| / (4 Ẑ_G(λ))`. Therefore, conditioned on sampling an independent set, `I` is distributed exactly according to `µλ`."
"The key observation is that the probability anything is sampled in a round is exactly `Z_G(λ)/(4Ẑ_G(λ))`." With p.33: `Z_X(λ) ≤ (1 + λ)^{|Y|} ≤ Z_G(λ)`.

**Formalization Note.** A finite algebraic statement about one round (`roundProb`), with no machine and no randomness in `G`. It holds for every bipartite `G`, all `α, β`, every positive estimate `Ẑj` and every positive proposal function `q`, so long as each
acceptance ratio is at most `1`. The p.33 bound needs `β = 4λ`. Both sums over orderings run over all orderings of the set. -/
theorem sampling_cases {m : ℕ} (G : SimpleGraph (Vertex m))
    (hG : ∀ u v, G.Adj u v → (u ∈ oddSide m ↔ v ∈ evenSide m)) (lam α β : ℝ) (hlam : 0 < lam)
    (Zh : Label → ℝ) (qT : ℕ → ℕ → Finset (Vertex m) → Vertex m → ℝ)
    (qO : Bool → ℕ → Finset (Vertex m) → Vertex m → ℝ)
    (hZT : ∀ kX kY, Label.two kX kY ∈ labels m α β → 0 < Zh (.two kX kY))
    (hZO : ∀ b k, Label.one b k ∈ labels m α β → 0 < Zh (.one b k))
    (hqT : ∀ kX kY, Label.two kX kY ∈ labels m α β → ∀ τ ∈ twoSidedComplex G kX kY,
      ∀ v ∈ HDXConc.linkVerts (twoSidedComplex G kX kY) τ, 0 < qT kX kY τ v)
    (hqO : ∀ b k, Label.one b k ∈ labels m α β → ∀ τ ∈ oneSidedComplex (sideOf m b) k,
      ∀ v ∈ HDXConc.linkVerts (oneSidedComplex (sideOf m b) k) τ, 0 < qO b k τ v)
    (hacT : ∀ kX kY, Label.two kX kY ∈ labels m α β → ∀ I ∈ twoSidedFacets G kX kY, ∀ L ∈ I.val.lists.toFinset,
      lam ^ (kX + kY) / (4 * ((kX + kY).factorial : ℝ) * Zh (.two kX kY) *
        seqProb (twoSidedComplex G kX kY) (qT kX kY) ∅ L) ≤ 1)
    (hacO : ∀ b k, Label.one b k ∈ labels m α β → ∀ S ∈ (sideOf m b).powersetCard k, ∀ L ∈ S.val.lists.toFinset,
      ∀ T ⊆ sideOf m (!b) \ vertexBoundary G S,
        (lam ^ (k + T.card) / (4 * (k.factorial : ℝ) * Zh (.one b k) *
            (seqProb (oneSidedComplex (sideOf m b) k) (qO b k) ∅ L *
              tLaw lam (sideOf m (!b) \ vertexBoundary G S) T))) *
          (1 / 2 : ℝ) ^ (if IsMed α β m T.card then 1 else 0) ≤ 1) :
    (∀ I : Finset (Vertex m), roundProb G lam α β Zh qT qO I =
      if IsIndependent G I then lam ^ I.card / (4 * ZhatG m lam α β Zh) else 0) ∧
    ∑ I : Finset (Vertex m), roundProb G lam α β Zh qT qO I = hardcoreZ G lam / (4 * ZhatG m lam α β Zh) ∧
    (β = 4 * lam → highZ m lam α β ≤ (1 + lam) ^ m ∧ (1 + lam) ^ m ≤ hardcoreZ G lam) := by sorry

end HardcoreSlices
