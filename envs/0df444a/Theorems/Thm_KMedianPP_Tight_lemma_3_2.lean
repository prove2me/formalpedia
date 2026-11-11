-- Prove2me | Theorems.Thm_KMedianPP_Tight_lemma_3_2
-- name    : KMedianPP.Tight.lemma_3_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T16:03:27.367707+00:00
-- url     : https://prove2.me/theorems/07d984d4-a6f0-41e8-9696-051744b8182e
-- title:
--   Lemma 3.2 — for $\ell=1$, $b(x)=\min\{D(w): d^*_w\le d^*_x\}$ is a balancing construction with $\alpha_1=2$
-- statement:
--   Let $\ell=1$ and, for $x$ in a cluster $P$, $b(x)=\min\{D(w):w\in P,\ d^*_w\le d^*_x\}$. For every nonempty center set $C$ and every cluster $P$:
--   1. the imbalanced mass of $P$ is at most $2\varphi(P)$: $\sum_{x\in P}(D(x)-b(x))\le2\varphi(P)$;
--   2. conditioned on the next sample being a hit of $P$ (sampled point $x$ with probability $b(x)/\sum_{y\in P}b(y)$, when this sum is positive), $\mathbb E[\mathrm{cost}(P,C\cup\{x\})\mid S,\text{hit of }P]\le2\varphi(P)$;
--   3. every $b(x)$ can only decrease as centers are added;
--   4. hence (P1)–(P3) hold with $\alpha_1=2$.
--
--   Differences from the source:
--   - encoding: a finite (multi)set X ⊆ M of input points → `X : Fin n → M` (input point i is `X i`; repeated points allowed); reason: a finite multiset is an indexed family; same instances
--   - encoding: current center set C ⊆ M, D(x) = d(x, C) → the indices `S : Finset (Fin n)` of the sampled input points, `D(x) = distTo X S x` (minimum over S); reason: D^ℓ-sampling only ever samples input points; same distances
--   - generalization: a fixed optimal solution with clusters P_1, …, P_k and optimal centers c*_1, …, c*_k (§2, p. 9) → any reference clustering: `σ : Fin n → Fin k` (P_j = {i : σ i = j}) and centers `c : Fin k → M`, with ϕ(P_j) = `phi X σ c ℓ j`; reason: the analysis never uses optimality or nearest-center assignment (only d*_x = d(x, c*_j) and the triangle inequality); an optimal solution is one such clustering, so the statement specializes to the source's
--   - generalization: P an unsettled optimal cluster (at the current state) → every cluster j at every nonempty center set S; reason: the bounds are properties of (C, P) only; settledness never enters them
--   - encoding: E[cost(P, C_new) | S, hit of P] → Σ_{x∈P} b(x)·cost(P, C ∪ {x}) / Σ_{x∈P} b(x), under 0 < Σ_{x∈P} b(x); reason: a hit of P has probability 0 otherwise
--   - reading: the sentence after the proof: "Monotonicity also holds, since every … b(x) can only decrease … Thus Properties (P1)–(P3) hold with α1 = 2" → clauses 3 (pointwise monotonicity) and 4 (`IsBalancingConstruction X σ c 1 2 b`); reason: the text after the lemma completes the statement used by §4
--   - encoding: D(x) (ℓ = 1) → `mass X 1 S i` = D(x)^1 (`Real.rpow`); reason: same values
-- source:
--   Kaplan, Naori, Tight Bounds for k-Median++ and Improved Bounds for k-Means++, STOC 2027 submission (manuscript sha256 f017529e…), p. 11 (PDF 13), Lemma 3.2 and the monotonicity sentence after its proof

import Mathlib
import Definitions.Def_KMedianPP_Tight_Sampling
import Definitions.Def_KMedianPP_Tight_Balancing

set_option autoImplicit false

namespace KMedianPP.Tight

/-- Lemma 3.2 (p. 11), with the monotonicity sentence after its proof: for `ℓ = 1` and the
balanced mass `b(x) = min {D(w) : w ∈ P, d*_w ≤ d*_x}`, the imbalanced mass of a cluster `P` is at
most `2ϕ(P)`; conditioned on a hit of `P`, the expected cost of `P` after the hit is at most
`2ϕ(P)`; every `b(x)` can only decrease as centers are added; hence (P1)–(P3) hold with
`α₁ = 2`. -/
theorem lemma_3_2 {M : Type*} [MetricSpace M] {n k : ℕ} (X : Fin n → M) (σ : Fin n → Fin k)
    (c : Fin k → M) (S : Finset (Fin n)) (hS : S.Nonempty) (j : Fin k) :
    (∑ i ∈ cluster σ j, (mass X 1 S i - balancedMassL1 X σ c S i) ≤ 2 * phi X σ c 1 j) ∧
    (0 < balMass σ (balancedMassL1 X σ c) S j →
      (∑ i ∈ cluster σ j, balancedMassL1 X σ c S i * clusterCost X σ 1 (insert i S) j) /
          balMass σ (balancedMassL1 X σ c) S j ≤ 2 * phi X σ c 1 j) ∧
    (∀ S' : Finset (Fin n), S ⊆ S' → ∀ i : Fin n,
      balancedMassL1 X σ c S' i ≤ balancedMassL1 X σ c S i) ∧
    IsBalancingConstruction X σ c 1 2 (balancedMassL1 X σ c) := by sorry

end KMedianPP.Tight
