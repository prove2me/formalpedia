-- Prove2me | Theorems.Thm_HighConfRobust_Supplement_theorem_6_5
-- name    : HighConfRobust.Supplement.theorem_6_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T10:44:12.790205+00:00
-- url     : https://prove2.me/theorems/96343286-4bcd-49a8-9aab-c60415bcc6cb
-- title:
--   Theorem 6.5 — a high-confidence $M$-ary tester yields a pure $\eta$-DP, $\rho$-replicable tester with additive sample overhead
-- statement:
--   Consider an $M$-ary hypothesis testing problem $(\mathcal F,\Theta)$: $\mathcal F=\bigcup_{j\in[M]}\mathcal H_j$ is a family of distributions on a sample space $\mathcal X$, the sets $\mathcal H_j$ are disjoint, and $\Theta(D)=j$ for $D\in\mathcal H_j$. An $n$-sample tester $A$ has **failure probability at most $\beta$** if $\Pr_{S\sim D^{\otimes n},\,\omega}[A(S,\omega)\ne\Theta(D)]\le\beta$ for every $D\in\mathcal F$.
--
--   There is a universal constant $C$ with the following property. Let $A$ be an $n$-sample tester for $(\mathcal F,\Theta)$ with failure probability at most $\beta$, fix a privacy parameter $\eta>0$ and a replicability parameter $\rho\in(0,1)$, and let $B=\log(1/\beta)$. Then there exist $\beta'>0$ with
--
--   $$
--   \beta'\le 2M\exp\Big(-\frac1{32}\min\big\{\eta B,\ \rho\sqrt B\big\}\Big)
--   $$
--
--   and a tester $A'$ for $(\mathcal F,\Theta)$ using at most
--
--   $$
--   N=2n+C\Big(\frac{\log(M/\beta')}{\eta}+\frac{\log^2(M/\beta')}{\rho^2}\Big)
--   $$
--
--   samples such that:
--
--   1. $A'$ is pure $\eta$-differentially private: for all datasets $S,S'$ differing in one sample and every set $E$ of outputs, $\Pr[A'(S)\in E]\le e^{\eta}\Pr[A'(S')\in E]$;
--   2. $A'$ is $\rho$-replicable: for every distribution $D$ on $\mathcal X$, two independent samples $S,S'\sim D^{\otimes N'}$ and a shared seed $r$, $\Pr[A'(S,r)\ne A'(S',r)]\le\rho$;
--   3. $A'$ has failure probability at most $\beta'$ on $(\mathcal F,\Theta)$.
--
--   A high-confidence tester thus yields private and replicable testers with an additive, rather than multiplicative, overhead in the privacy and replicability parameters.
--
--   **Formalization Note** $\Theta$ is a map from distributions to $\mathrm{Fin}\,M$ and the tester's failure is the published high-confidence predicate with the zero-one loss and error $0$. The tester $A'$ is the published randomized algorithm with explicit coins (jointly measurable), privacy is the published pure-DP predicate on its output laws, and replicability is the published replicability predicate at every distribution. The constant $C$ is quantified before everything else.
--
--   Differences from the source:
--   - encoding: M-ary problem with disjoint classes H_1, …, H_M, F = ∪ H_j, Θ(D) = j for D ∈ H_j → F : Set (ProbabilityMeasure X) and Θ : ProbabilityMeasure X → Fin M; reason: H_j = F ∩ Θ⁻¹(j) are disjoint automatically; every such problem arises this way
--   - generalization: M ≥ 2 (Example 1.2) → 1 ≤ M; reason: for M = 1 a constant tester satisfies the conclusion; at M ≥ 2 the statement is the page's
--   - encoding: n-sample tester with failure probability at most β → IsHighConfidence with the zero-one loss, error 0, A : (Fin n → X) → Ω → Fin M jointly measurable with a probability seed law; reason: the failure set of the zero-one loss at error 0 is {A ≠ Θ D}; algorithms are measurable by the standing convention
--   - encoding: B = log(1/β) → hypothesis 0 < β; reason: at β = 0 the page's B and N are infinite, while Lean's log(1/0) = 0 would turn the bound on β′ into a trivial one
--   - encoding: β′ in log(M/β′) and the failure bound → ∃ β′ with 0 < β′; reason: log(M/β′) needs β′ > 0
--   - encoding: using at most N samples → ∃ N′ : ℕ with N′ ≤ N and A′ on N′ samples; reason: literal reading
--   - generalization: a tester A′ (a randomized algorithm) → A′ a DPVerify.RandAlg (explicit coin space, jointly measurable map); reason: a stronger conclusion; it holds because the user-level score D_{j,ω} of §6.2 (finitely many evaluations of A, sensitivity 1 by Claim 6.10 (ii)) gives a measurable exponential mechanism with the same constants, followed by a measurable correlated-sampling scheme
--   - encoding: η-private, datasets differing in at most one sample, measurable events (Definition 1.6) → PrivLearn.Generic.IsDP A′.law η (datasets differing in exactly one coordinate, measurable sets); reason: for equal datasets the inequality is trivial
--   - encoding: Pr(A′(S, r) ≠ A′(S′, r)) ≤ ρ for all distributions D (Definition 1.7) → DPVerify.IsReplicableAt A′ D ρ (agreement ≥ 1 − ρ) for every D : ProbabilityMeasure X; reason: the agreement set is measurable for a jointly measurable A′, so the two are equivalent
--   - encoding: sample space X, seed space of A → X, Ω : Type; reason: the published RandAlg lives in Type; every concrete sample space is in Type
-- source:
--   Narayanan–Lee–Pensia, High Confidence Yields Outlier Robustness, STOC 2027 submission manuscript, Nov. 3, 2026 (sha256 f0e4ec41…c370c153), Theorem 6.5, p.25 (setting of §6, p.24; Example 1.2, p.4; Definitions 1.3, 1.6, 1.7, p.5; informal Theorem 1.17, p.10)

import Mathlib
import Definitions.Def_HighConfRobust_IsHighConfidence
import Definitions.Def_DPVerify_RandAlg
import Definitions.Def_DPVerify_IsReplicableAt
import Definitions.Def_PrivLearn_Generic_Privacy

namespace HighConfRobust.Supplement

open MeasureTheory

/-- **Theorem 6.5** (p.25; informal version Theorem 1.17, p.10). There is a universal constant `C`
such that: let `A` be an `n`-sample tester for the `M`-ary hypothesis testing problem `(F, Θ)` with
failure probability at most `β`, fix `η > 0`, `ρ ∈ (0, 1)` and let `B = log(1/β)`. Then there is a
pure `η`-differentially private, `ρ`-replicable tester `A'` for `(F, Θ)` with failure probability at
most `β'` using at most `N` samples, where
`N = 2n + C (log(M/β')/η + log²(M/β')/ρ²)` and `β' ≤ 2M exp(−(1/32) min{ηB, ρ√B})`.

Narayanan–Lee–Pensia, *High Confidence Yields Outlier Robustness: Consequences in Computational
Hardness, Privacy, and Replicability*, STOC 2027 submission manuscript, Nov. 3, 2026
(sha256 f0e4ec41…c370c153), Theorem 6.5, p.25 (setting of §6, p.24; Example 1.2, p.4;
Definitions 1.3, 1.6, 1.7, pp.5; informal Theorem 1.17, p.10).

**Formalization Note**
* `(F, Θ)`: `F` a set of distributions and `Θ : ProbabilityMeasure X → Fin M`; `H_j = F ∩ Θ⁻¹(j)`.
  A tester with failure probability at most `β` is `IsHighConfidence` with the zero-one loss and
  error `0` (failure set `{A(S, ω) ≠ Θ D}`). `A` is jointly measurable with seed law `ν`.
* `C` is quantified first: it depends on nothing.
* `A'` is a published `DPVerify.RandAlg X (Fin M) N'` (explicit coins, jointly measurable) on
  `N' ≤ N` samples. Privacy is the published `PrivLearn.Generic.IsDP` of its output laws (neighbours
  differ in exactly one sample; for equal datasets the inequality is trivial, so this is the page's
  "at most one"). Replicability is the published `DPVerify.IsReplicableAt` at **every** distribution
  on `X` (agreement `≥ 1 − ρ`, i.e. disagreement `≤ ρ`).
* `B = log(1/β)` with `0 < β`; `1 ≤ M`; `0 < β'` (the page takes `log(M/β')`). -/
theorem theorem_6_5 :
    ∃ C : ℝ, ∀ (X : Type) [MeasurableSpace X] (M : ℕ), 1 ≤ M →
      ∀ (F : Set (ProbabilityMeasure X)) (Θ : ProbabilityMeasure X → Fin M) (n : ℕ)
        (Ω : Type) [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
        (A : (Fin n → X) → Ω → Fin M), Measurable (Function.uncurry A) →
        ∀ β : ℝ, 0 < β →
        HighConfRobust.IsHighConfidence (fun y y' : Fin M => if y = y' then (0 : ℝ) else 1)
          Θ A ν 0 β F →
        ∀ η ρ : ℝ, 0 < η → 0 < ρ → ρ < 1 →
        ∃ β' : ℝ, 0 < β' ∧
          β' ≤ 2 * M * Real.exp (-(1 / 32) *
            min (η * Real.log (1 / β)) (ρ * Real.sqrt (Real.log (1 / β)))) ∧
          ∃ N' : ℕ, (N' : ℝ) ≤ 2 * n + C * (Real.log (M / β') / η + Real.log (M / β') ^ 2 / ρ ^ 2) ∧
          ∃ A' : DPVerify.RandAlg X (Fin M) N',
            PrivLearn.Generic.IsDP A'.law η ∧
            (∀ D : ProbabilityMeasure X, DPVerify.IsReplicableAt A' D ρ) ∧
            HighConfRobust.IsHighConfidence (fun y y' : Fin M => if y = y' then (0 : ℝ) else 1)
              Θ A'.run A'.P 0 β' F := by sorry

end HighConfRobust.Supplement
