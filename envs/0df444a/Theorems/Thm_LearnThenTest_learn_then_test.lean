-- Prove2me | Theorems.Thm_LearnThenTest_learn_then_test
-- name    : LearnThenTest.learn_then_test
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-24T00:13:31.346945+00:00
-- url     : https://prove2.me/theorems/7a77a5d0-79ee-456a-858e-f392cc85672f
-- title:
--   Theorem 1: Learn then Test — FWER control yields risk control
-- statement:
--   Let $\Lambda=\{\lambda_1,\dots,\lambda_N\}$ be a finite parameter grid with risks $R(\lambda_j)$, let $\alpha,\delta\in\mathbb R$, and let $\mathcal H_j:R(\lambda_j)>\alpha$. Let $p_1,\dots,p_N$ be p-values with values in $[0,1]$, defined on one probability space and arbitrarily dependent. Suppose that whenever $\mathcal H_j$ holds, $p_j$ stochastically dominates the uniform distribution: $\mathbb P(p_j\le u)\le u$ for all $u\in[0,1]$. Let $\mathcal A$ be an FWER-controlling algorithm at level $\delta$, and let $\hat\Lambda=\mathcal A(p_1,\dots,p_N)$. Then
--
--   $$\mathbb P\Big(\sup_{\lambda\in\hat\Lambda}R(\lambda)\le\alpha\Big)\ge1-\delta,$$
--
--   where the supremum over the empty set is $-\infty$.
--
--   Consequently, if a selection rule $\hat\lambda$ picks an element of $\hat\Lambda$ whenever $\hat\Lambda\ne\emptyset$, then with probability at least $1-\delta$, either $\hat\Lambda=\emptyset$ (and the procedure abstains) or $R(\hat\lambda)\le\alpha$. In particular, if $\hat\Lambda$ is never empty, then $\mathcal T_{\hat\lambda}$ is an $(\alpha,\delta)$-RCP.
--
--   This is the main result of the paper. It reduces risk control for an arbitrary, possibly non-monotone, risk to computing valid p-values and running an FWER-controlling procedure.
--
--   **Formalization Note** The supremum is taken in $\mathbb R\cup\{-\infty\}$. The paper's "selecting any $\lambda\in\hat\Lambda$, $\mathcal T_\lambda$ is an $(\alpha,\delta)$-RCP" is stated for a selection rule that may abstain when $\hat\Lambda=\emptyset$, which is the paper's convention in Section 1.1. Requiring $\hat\Lambda\ne\emptyset$ on every outcome would make the hypothesis unsatisfiable in typical cases. The p-values are measurable and take values in $[0,1]$, the domain of $\mathcal A$ in Definition 2.
-- source:
--   Angelopoulos, Bates, Candès, Jordan and Lei, Learn then Test: Calibrating Predictive Algorithms to Achieve Risk Control, arXiv:2110.01052v5 (2022), Section 2.1, Theorem 1, p. 3; proof in Appendix C, p. 22

import Mathlib
import Definitions.Def_LearnThenTest_Basic

open MeasureTheory ProbabilityTheory Filter

namespace LearnThenTest

theorem learn_then_test {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {N : ℕ} (R : Fin N → ℝ) (α δ : ℝ) (p : Fin N → Ω → ℝ)
    (hp : ∀ j, Measurable (p j)) (hp01 : ∀ j ω, p j ω ∈ Set.Icc (0 : ℝ) 1)
    (hvalid : ∀ j, α < R j → IsValidPValue P (p j))
    (A : (Fin N → ℝ) → Finset (Fin N)) (hA : IsFWERControlling N δ A) :
    ENNReal.ofReal (1 - δ) ≤
      P {ω | (A (fun j => p j ω)).sup (fun j => (R j : WithBot ℝ)) ≤ (α : WithBot ℝ)} ∧
    ∀ lhat : Ω → Fin N,
      (∀ ω, (A (fun j => p j ω)).Nonempty → lhat ω ∈ A (fun j => p j ω)) →
      ENNReal.ofReal (1 - δ) ≤
        P {ω | (A (fun j => p j ω)).Nonempty → R (lhat ω) ≤ α} := by sorry

end LearnThenTest
