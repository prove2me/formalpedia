-- Prove2me | Theorems.Thm_MemoryRegret_proposition_5_posterior
-- name    : MemoryRegret.proposition_5_posterior
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:41:45.070255+00:00
-- url     : https://prove2.me/theorems/8f93cf34-ae98-4f9e-a20f-57d9719527fb
-- title:
--   Proposition 5 — a low-memory learner learns little about the hidden hypothesis
-- statement:
--   There is an absolute constant $K$ with the following property. Let $0<\varepsilon<1/(10^3r)$, $1\le m\le1/(10^6\varepsilon^2r^2)$, let $\mu$ be a distribution on a finite set $X$ and $H$ a finite nonempty class whose matrix $M(x,h)=(-1)^{h(x)}$ is a $(k,\ell)$-$L_2$-extractor with error $2^{-r}$ with respect to $\mu$, and put $r_{\min}=\min(r,k,\ell)/5$. Let $B$ be a branching program of width $d\le2^{k\ell/(10^4\varepsilon r\sqrt m)}$ and length $\tau\le2^{r_{\min}}$ for the learning problem in which $h$ is uniform on $H$ and at each step the learner sees $(x_t,b_t)$ with $x_t\sim\mu$ and $b_t^{(i)}\sim\mathrm{Ber}(h(x_t),\frac12+\varepsilon)$. Then there is an event $\mathcal E$, on the samples and the hidden hypothesis, such that
--   $$\Pr(\mathcal E)\ge1-K\,2^{-r_{\min}}$$
--   and, for every leaf vertex $v$, the law $\mathbb P^{\mathcal E}_{h|v}$ of $h$ given that the computation path reaches $v$ and $\mathcal E$ holds satisfies
--   $$\bigl\|\mathbb P^{\mathcal E}_{h|v}\bigr\|_2\le\frac{2^\ell}{|H|}.$$
--
--   This is the memory-sample tradeoff for the learning problem with blocks of labels, and it drives the hybrid argument for Theorem 4.
--
--   **Formalization Note** $\|\cdot\|_2$ is with respect to the uniform distribution on the class, so the uniform law has norm $1/|H|$.
--
--   Differences from the source:
--   - encoding: O(2^{−r_min}) → K·2^{−r_min} with K absolute and quantified first; reason: the standard meaning
--   - encoding: k, ℓ, r sufficiently large, as assumed in the proof → no threshold stated; reason: equivalent: below any threshold the event ℰ = ∅ satisfies the statement for a large K
--   - encoding: for all leaf vertices v → for all leaf vertices (i, v) that the path reaches together with ℰ with positive probability; reason: the conditional law is undefined elsewhere
--   - encoding: ε < 1/(10³r) and m ≤ 1/(10⁶ε²r²) → ε·10³r < 1 and m·10⁶ε²r² ≤ 1; reason: multiplicative form avoids x/0 = 0; the same instances for r > 0
--   - generalization: the class H ⊆ {0,1}^X with h uniform on H → an indexed family hyp : ι → X → Bool with i uniform on ι; reason: ι = H with hyp h = h is the source statement; the family form also covers the [d]-indexed matrix of Lemma 4.1 and allows repetitions
--   - encoding: branching program with at most d vertices per layer and width bound on d → one finite state type S per program, with width |S|; reason: a width-d program is the case S = Fin d
-- source:
--   Brukhim, Garg, Memory-Regret Tradeoffs for Online Learning (manuscript, sha256 89bb0279…), Proposition 5, pp.9–10

import Mathlib
import Definitions.Def_MemoryRegret_IsProbVec
import Definitions.Def_MemoryRegret_IsL2Extractor
import Definitions.Def_MemoryRegret_streamD1
import Definitions.Def_MemoryRegret_BranchingProgram
import Definitions.Def_MemoryRegret_truncAlive

namespace MemoryRegret

/-- **Proposition 5 (a low-memory learner learns little about the hidden hypothesis).**
Brukhim, Garg, *Memory-Regret Tradeoffs for Online Learning* (manuscript, sha256 89bb0279…),
Proposition 5, pp.9–10.

There is an absolute constant `K` such that: let `0 < ε < 1/(10³r)`, `1 ≤ m ≤ 1/(10⁶ε²r²)`,
`µ` a distribution on a finite `X`, `(hyp i)_{i∈ι}` a finite nonempty class whose matrix
`M(x, h) = (−1)^{h(x)}` is a `(k, ℓ)`-L2-extractor with error `2^{−r}` w.r.t. `µ`, and
`r_min = min(r, k, ℓ)/5`. Let `B` be a branching program of width `d ≤ 2^{kℓ/(10⁴ε·r√m)}` and
length `τ ≤ 2^{r_min}` for the learning problem in which `h` is uniform on the class and at each
step the learner sees `(x_t, b_t)` with `x_t ∼ µ` and `b_t^{(i)} ∼ Ber(h(x_t), ½ + ε)`. Then
there is an event `ℰ` (on the hidden hypothesis and the samples) with
`Pr(ℰ) ≥ 1 − K·2^{−r_min}` such that, for every leaf vertex `v`,
`‖P^ℰ_{h|v}‖₂ ≤ 2^ℓ/|H|`, where `P^ℰ_{h|v}` is the law of `h` given that the computation path
reaches `v` and `ℰ` holds.

**Formalization Note.** `O(2^{−r_min})` is `K·2^{−r_min}` with `K` absolute and chosen first;
no "sufficiently large" threshold is needed (below it, `ℰ = ∅` satisfies the statement for a
large `K`). The posterior is `postAt (jointLaw µ hyp ε) B ℰ i v`; the bound is required at the
leaves `(i, v)` that the path reaches together with `ℰ` with positive probability (elsewhere
the conditional law is undefined). `‖·‖₂` is with respect to the uniform distribution on `ι`,
so the uniform law has norm `1/|ι|`. Ratios are written multiplicatively. -/
theorem proposition_5_posterior :
    ∃ K : ℝ, ∀ (X : Type) [Fintype X] (μ : X → ℝ), IsProbVec μ →
      ∀ (ι : Type) [Fintype ι] [Nonempty ι] (hyp : ι → X → Bool) (k ℓ r ε : ℝ) (m τ : ℕ)
        (S : Type) [Fintype S] (B : BranchingProgram S (X × (Fin m → Bool)) τ),
        IsL2Extractor μ hyp k ℓ r → 0 < ε → ε * (10 ^ 3 * r) < 1 → 1 ≤ m →
        (m : ℝ) * (10 ^ 6 * ε ^ 2 * r ^ 2) ≤ 1 →
        (Fintype.card S : ℝ) ≤ (2 : ℝ) ^ (k * ℓ / (10 ^ 4 * ε * r * Real.sqrt m)) →
        (τ : ℝ) ≤ (2 : ℝ) ^ (min r (min k ℓ) / 5) →
        ∃ E : Set (ι × (Fin τ → X × (Fin m → Bool))),
          1 - K * (2 : ℝ) ^ (-(min r (min k ℓ) / 5)) ≤ wprob (jointLaw μ hyp ε) (· ∈ E) ∧
          ∀ (i : ℕ) (v : S), B.IsLeafVertex i v →
            0 < wprob (jointLaw μ hyp ε) (fun p => p ∈ E ∧ B.Reaches p.2 i v) →
            unifNorm2 (postAt (jointLaw μ hyp ε) B E i v) ≤ (2 : ℝ) ^ ℓ / Fintype.card ι := by sorry

end MemoryRegret
