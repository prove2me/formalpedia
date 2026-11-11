-- Prove2me | Theorems.Thm_KMedianPP_Tight_theorem_4_5
-- name    : KMedianPP.Tight.theorem_4_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T16:03:27.852098+00:00
-- url     : https://prove2.me/theorems/91bd25b7-5788-47d1-b49a-92618e702cb9
-- title:
--   Theorem 4.5 — $\mathbb E[\mathrm{cost}(C_{\mathrm{final}})]\le\alpha_\ell B_{k,\Delta}\,\mathrm{OPT}$ for every balancing constant $\alpha_\ell$
-- statement:
--   For all integers $k\ge1$, $\Delta\ge0$ and every $\ell>0$: on every instance, if a balancing construction with constant $\alpha$ satisfies (P1)–(P3) and every cluster satisfies the first-sample bound $\mathbb E[\mathrm{cost}(P,\{Z\})]\le\alpha\varphi(P)$ ($Z$ uniform in $P$; Lemma 3.1), then after sampling $k+\Delta$ centers by $D^\ell$-sampling
--   $$\mathbb E[\mathrm{cost}(C_{\mathrm{final}})]\le\alpha\,B_{k,\Delta}\sum_{j}\varphi(P_j),$$
--   for every reference clustering $P_1,\dots,P_k$ with centers $c^*_1,\dots,c^*_k$; with an optimal one, $\sum_j\varphi(P_j)=\mathrm{OPT}$.
--
--   Differences from the source:
--   - encoding: a finite (multi)set X ⊆ M of input points → `X : Fin n → M` (input point i is `X i`; repeated points allowed); reason: a finite multiset is an indexed family; same instances
--   - encoding: the first center is sampled uniformly from X (X implicitly nonempty) → hypothesis `0 < n`; reason: excludes only the empty input, on which the algorithm is undefined
--   - encoding: current center set C ⊆ M, D(x) = d(x, C) → the indices `S : Finset (Fin n)` of the sampled input points, `D(x) = distTo X S x` (minimum over S); reason: D^ℓ-sampling only ever samples input points; same distances
--   - generalization: a fixed optimal solution with clusters P_1, …, P_k and optimal centers c*_1, …, c*_k (§2, p. 9) → any reference clustering: `σ : Fin n → Fin k` (P_j = {i : σ i = j}) and centers `c : Fin k → M`, with ϕ(P_j) = `phi X σ c ℓ j`; reason: the analysis never uses optimality or nearest-center assignment (only d*_x = d(x, c*_j) and the triangle inequality); an optimal solution is one such clustering, so the statement specializes to the source's
--   - encoding: §2 standing assumption: a fixed distance exponent ℓ > 0 → hypothesis `0 < ℓ`; reason: the section's standing assumption made explicit
--   - encoding: D(x)^ℓ, (d*_x)^ℓ for real ℓ > 0 → `Real.rpow` (`^` with a real exponent) of nonnegative reals; reason: same values
--   - encoding: E[cost(C_final)] over the algorithm's random choices → `expectedCost X ℓ k Δ`: (1/n) Σ_i of the exact recursion `expFinalCostFrom` over the k + Δ − 1 remaining D^ℓ-samples from {x_i}; reason: the exact finite expectation of the same Markov chain
--   - encoding: footnote 4: if cost(C) = 0 the algorithm terminates → the expectation recursions return the current value when `totalCost = 0`; reason: same process; the next-sample law is undefined there
--   - reading: α_ℓ in "E[cost(C_final)] ≤ α_ℓ B_{k,Δ} OPT" (not defined in the theorem; §3 p. 10, §4 p. 14: the constant of a balancing construction satisfying (P1)–(P3)) → α with balanced masses b and `IsBalancingConstruction X σ c ℓ α b` on the instance; reason: the meaning given at the start of §4: "we use only Properties (P1)–(P3) … with the corresponding balancing constant α_ℓ"
--   - generalization: the construction is a rule on all inputs, and the first center's cluster is bounded by Lemma 3.1 (eq. (9)), whose proof uses the rule on an auxiliary input P ∪ {q} → the construction only on this instance, plus the hypothesis `∀ j, FirstSampleBound X σ c ℓ α j` (the conclusion of Lemma 3.1); reason: a rule satisfying (P1)–(P3) for the optimal clusters of every input yields both hypotheses for an optimal reference clustering (Lemma 3.1 gives the second), so the statement specializes to the source's
-- source:
--   Kaplan, Naori, Tight Bounds for k-Median++ and Improved Bounds for k-Means++, STOC 2027 submission (manuscript sha256 f017529e…), p. 16 (PDF 18), Theorem 4.5 and the definition of B_{k,Δ}; proof pp. 18–23 (PDF 20–25)

import Mathlib
import Definitions.Def_KMedianPP_Tight_Sampling
import Definitions.Def_KMedianPP_Tight_EqualMass
import Definitions.Def_KMedianPP_Tight_Balancing

set_option autoImplicit false

namespace KMedianPP.Tight

/-- Theorem 4.5 (p. 16): for all integers `k ≥ 1` and `Δ ≥ 0`, after sampling `k + Δ` centers by
`D^ℓ`-sampling, `E[cost(C_final)] ≤ α B_{k,Δ} OPT`, where `α` is the constant of a balancing
construction satisfying (P1)–(P3) together with the first-sample bound of Lemma 3.1; stated
against every reference clustering in place of a fixed optimal one. -/
theorem theorem_4_5 {M : Type*} [MetricSpace M] {n k : ℕ} (hk : 1 ≤ k) (Δ : ℕ) (hn : 0 < n)
    (X : Fin n → M) (σ : Fin n → Fin k) (c : Fin k → M) (ℓ α : ℝ) (hℓ : 0 < ℓ)
    (b : Finset (Fin n) → Fin n → ℝ) (hb : IsBalancingConstruction X σ c ℓ α b)
    (hfirst : ∀ j : Fin k, FirstSampleBound X σ c ℓ α j) :
    expectedCost X ℓ k Δ ≤ α * B k Δ * refCost X σ c ℓ := by sorry

end KMedianPP.Tight
