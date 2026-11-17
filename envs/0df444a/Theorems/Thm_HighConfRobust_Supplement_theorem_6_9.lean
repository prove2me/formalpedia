-- Prove2me | Theorems.Thm_HighConfRobust_Supplement_theorem_6_9
-- name    : HighConfRobust.Supplement.theorem_6_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T10:44:45.662063+00:00
-- url     : https://prove2.me/theorems/a112d9b9-6374-423b-93fa-2d303b820a05
-- title:
--   Theorem 6.9 — a $\rho$-replicable tester with at most $2n+2\lceil 128/\rho^2\rceil$ samples and failure at most $4^{\lceil 128/\rho^2\rceil}\beta$
-- statement:
--   Consider an $M$-ary hypothesis testing problem $(\mathcal F,\Theta)$ on a sample space $\mathcal X$: $\mathcal F=\bigcup_{j\in[M]}\mathcal H_j$ with disjoint classes $\mathcal H_j$ and $\Theta(D)=j$ for $D\in\mathcal H_j$. Let $A$ be an $n$-sample tester with failure probability at most $\beta$, i.e. $\Pr_{S\sim D^{\otimes n},\,\omega}[A(S,\omega)\ne\Theta(D)]\le\beta$ for every $D\in\mathcal F$, and let $\rho\in(0,1)$. Write $k=\lceil 128/\rho^2\rceil$. Then there is a tester $A'$ using at most
--
--   $$
--   2n+2\Big\lceil\frac{128}{\rho^2}\Big\rceil
--   $$
--
--   samples such that
--
--   1. $A'$ is $\rho$-replicable: for every distribution $D$ on $\mathcal X$, two independent samples $S,S'$ from $D$ and a shared seed $r$, $\Pr[A'(S,r)\ne A'(S',r)]\le\rho$;
--   2. $A'$ has failure probability at most
--
--   $$
--   \beta'\le 4^{\lceil 128/\rho^2\rceil}\,\beta
--   $$
--
--   on $(\mathcal F,\Theta)$.
--
--   The replicability overhead is additive and independent of $M$; with $\log(1/\beta)\gtrsim\rho^{-2}$ the failure probability stays small.
--
--   **Formalization Note** The problem, the tester and its failure are encoded as in Theorem 6.5 of this mission (zero-one loss, error $0$). $A'$ is the published randomized algorithm with explicit coins, and replicability is the published replicability predicate at every distribution on $\mathcal X$.
--
--   Differences from the source:
--   - encoding: M-ary problem with disjoint classes H_1, …, H_M, F = ∪ H_j, Θ(D) = j for D ∈ H_j → F : Set (ProbabilityMeasure X) and Θ : ProbabilityMeasure X → Fin M; reason: H_j = F ∩ Θ⁻¹(j) are disjoint automatically; every such problem arises this way
--   - generalization: M ≥ 2 (Example 1.2) → 1 ≤ M; reason: for M = 1 a constant tester satisfies the conclusion; at M ≥ 2 the statement is the page's
--   - encoding: n-sample tester with failure probability at most β → IsHighConfidence with the zero-one loss, error 0, A : (Fin n → X) → Ω → Fin M jointly measurable with a probability seed law; reason: the failure set of the zero-one loss at error 0 is {A ≠ Θ D}; algorithms are measurable by the standing convention
--   - encoding: using at most 2n + 2⌈128/ρ²⌉ samples → ∃ N′ : ℕ with N′ ≤ 2n + 2⌈128/ρ²⌉₊ and A′ on N′ samples; reason: literal reading, ⌈·⌉ as Nat.ceil of a positive real
--   - generalization: a ρ-replicable tester A′ (a randomized algorithm) → A′ a DPVerify.RandAlg (explicit coin space, jointly measurable map); reason: a stronger conclusion; the construction of the proof (finitely many evaluations of A, the weights W_{j,ω}, correlated sampling) is measurable when A is
--   - encoding: Pr(A′(S, r) ≠ A′(S′, r)) ≤ ρ for all distributions D (Definition 1.7) → DPVerify.IsReplicableAt A′ D ρ (agreement ≥ 1 − ρ) for every D : ProbabilityMeasure X; reason: the agreement set is measurable for a jointly measurable A′, so the two are equivalent
--   - encoding: sample space X, seed space of A → X, Ω : Type; reason: the published RandAlg lives in Type; every concrete sample space is in Type
-- source:
--   Narayanan–Lee–Pensia, High Confidence Yields Outlier Robustness, STOC 2027 submission manuscript, Nov. 3, 2026 (sha256 f0e4ec41…c370c153), Theorem 6.9, p.28 (setting of §6, p.24; Example 1.2, p.4; Definitions 1.3, 1.7, p.5)

import Mathlib
import Definitions.Def_HighConfRobust_IsHighConfidence
import Definitions.Def_DPVerify_RandAlg
import Definitions.Def_DPVerify_IsReplicableAt

namespace HighConfRobust.Supplement

open MeasureTheory

/-- **Theorem 6.9** (sharper replicable tester, p.28). Consider an `M`-ary hypothesis testing
problem `(F, Θ)`. Given an `n`-sample tester `A` with failure probability at most `β`, there is a
`ρ`-replicable tester `A'` using at most `2n + 2⌈128/ρ²⌉` samples with failure probability at most
`4^{⌈128/ρ²⌉} β`.

Narayanan–Lee–Pensia, *High Confidence Yields Outlier Robustness: Consequences in Computational
Hardness, Privacy, and Replicability*, STOC 2027 submission manuscript, Nov. 3, 2026
(sha256 f0e4ec41…c370c153), Theorem 6.9, p.28 (setting of §6, p.24; Example 1.2, p.4;
Definitions 1.3, 1.7, p.5).

**Formalization Note**
* `(F, Θ)`, the tester `A` and its failure probability are encoded as in `theorem_6_5`
  (zero-one loss, error `0`, `A` jointly measurable with seed law `ν`).
* `A'` is a published `DPVerify.RandAlg X (Fin M) N'` with `N' ≤ 2n + 2⌈128/ρ²⌉` (`Nat.ceil`),
  replicable at **every** distribution on `X`, with the failure bound on `F`.
* `1 ≤ M` and `ρ ∈ (0, 1)` (Definition 1.7); no condition on `β` or `n`, as on the page. -/
theorem theorem_6_9 {X : Type} [MeasurableSpace X] (M : ℕ) (hM : 1 ≤ M)
    (F : Set (ProbabilityMeasure X)) (Θ : ProbabilityMeasure X → Fin M) (n : ℕ)
    {Ω : Type} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
    (A : (Fin n → X) → Ω → Fin M) (hA : Measurable (Function.uncurry A)) (β : ℝ)
    (hHC : HighConfRobust.IsHighConfidence (fun y y' : Fin M => if y = y' then (0 : ℝ) else 1)
      Θ A ν 0 β F)
    (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    ∃ N' : ℕ, N' ≤ 2 * n + 2 * ⌈128 / ρ ^ 2⌉₊ ∧
      ∃ A' : DPVerify.RandAlg X (Fin M) N',
        (∀ D : ProbabilityMeasure X, DPVerify.IsReplicableAt A' D ρ) ∧
        HighConfRobust.IsHighConfidence (fun y y' : Fin M => if y = y' then (0 : ℝ) else 1)
          Θ A'.run A'.P 0 ((4 : ℝ) ^ ⌈128 / ρ ^ 2⌉₊ * β) F := by sorry

end HighConfRobust.Supplement
