-- Prove2me | Theorems.Thm_KMedianPP_Tight_lemma_3_1
-- name    : KMedianPP.Tight.lemma_3_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T16:03:27.524785+00:00
-- url     : https://prove2.me/theorems/b3144f51-cf98-4b8e-a768-9d4f32f0bc89
-- title:
--   Lemma 3.1 — (P1) and (P2) with constant $\alpha_\ell$ imply $\mathbb E[\mathrm{cost}(P,\{Z\})]\le\alpha_\ell\varphi(P)$ for $Z$ uniform in $P$
-- statement:
--   Let $\ell>0$ and let $F$ be a balancing construction (balanced masses on every instance of every metric space) that splits the sampling masses and satisfies (P1) and (P2) with constant $\alpha$ for the optimal clusters of every instance. Then for every instance, every optimal solution (reference clustering whose cost is at most that of every set of $1$ to $k$ centers), every optimal cluster $P$ and a uniformly random point $Z\in P$,
--   $$\mathbb E[\mathrm{cost}(P,\{Z\})]\le\alpha\,\varphi(P),\qquad\text{i.e.}\quad \sum_{z\in P}\sum_{x\in P}d(x,z)^\ell\le\alpha\,|P|\,\varphi(P).$$
--
--   Differences from the source:
--   - encoding: a finite (multi)set X ⊆ M of input points → `X : Fin n → M` (input point i is `X i`; repeated points allowed); reason: a finite multiset is an indexed family; same instances
--   - encoding: an optimal solution with clusters P_1, …, P_k and optimal centers c*_1, …, c*_k (§2, p. 9) → a reference clustering `σ : Fin n → Fin k` (P_j = {i : σ i = j}), `c : Fin k → M` with `IsOptimalClustering X σ c ℓ` (cost Σ_i d(x_i, c_{σ i})^ℓ at most cost(X, C) for every C ⊆ M with 1 ≤ |C| ≤ k), with ϕ(P_j) = `phi X σ c ℓ j`; reason: k points possibly coinciding; minimal cost forces each point to a nearest center (ties arbitrary); same optimal clusters
--   - encoding: §2 standing assumption: a fixed distance exponent ℓ > 0 → hypothesis `0 < ℓ`; reason: the section's standing assumption made explicit
--   - encoding: D(x)^ℓ, (d*_x)^ℓ for real ℓ > 0 → `Real.rpow` (`^` with a real exponent) of nonnegative reals; reason: same values
--   - reading: "a balancing construction satisfies Properties (P1) and (P2) with constant α_ℓ" → a `BalancingRule` F (balanced masses for every metric space in a universe u, every finite input and reference clustering) with `SatisfiesP1P2 F ℓ α` ((P1), (P2) for the optimal clusters of every instance); reason: a construction is a rule for every input; the proof (App. A, p. 30) applies it to the auxiliary input P ∪ {q} with a far point q
--   - encoding: E[cost(P, {Z})] ≤ α_ℓ ϕ(P) for Z uniform in P → Σ_{z∈P} Σ_{x∈P} d(x, z)^ℓ ≤ α·|P|·ϕ(P) (`FirstSampleBound`); reason: multiplied by |P|; the same for P ≠ ∅ and 0 ≤ 0 for P = ∅
--   - encoding: metric spaces of any size → metric spaces in a fixed universe `Type u` (the rule and the instance in the same universe); reason: universe bookkeeping; u is arbitrary
-- source:
--   Kaplan, Naori, Tight Bounds for k-Median++ and Improved Bounds for k-Means++, STOC 2027 submission (manuscript sha256 f017529e…), p. 10 (PDF 12), Lemma 3.1; proof App. A, pp. 30–31 (PDF 32–33)

import Mathlib
import Definitions.Def_KMedianPP_Tight_Sampling
import Definitions.Def_KMedianPP_Tight_Balancing

set_option autoImplicit false

universe u

namespace KMedianPP.Tight

/-- Lemma 3.1 (p. 10; proof App. A, pp. 30–31): if a balancing construction satisfies (P1) and
(P2) with constant `α` (for the optimal clusters of every instance), then for every optimal
cluster `P` and a uniformly random point
`Z ∈ P`, `E[cost(P, {Z})] ≤ α ϕ(P)`. -/
theorem lemma_3_1 (ℓ α : ℝ) (hℓ : 0 < ℓ) (F : BalancingRule.{u}) (hF : SatisfiesP1P2 F ℓ α)
    {M : Type u} [MetricSpace M] {n k : ℕ} (X : Fin n → M) (σ : Fin n → Fin k) (c : Fin k → M)
    (hopt : IsOptimalClustering X σ c ℓ) (j : Fin k) :
    FirstSampleBound X σ c ℓ α j := by sorry

end KMedianPP.Tight
