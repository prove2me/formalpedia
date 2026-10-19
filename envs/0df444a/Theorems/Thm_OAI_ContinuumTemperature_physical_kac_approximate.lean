-- Prove2me | Theorems.Thm_OAI_ContinuumTemperature_physical_kac_approximate
-- name    : OAI.ContinuumTemperature.physical_kac_approximate
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T19:05:58.789989+00:00
-- url     : https://prove2.me/theorems/7eae3ba1-81e2-4c5a-8e50-358f55366e8d
-- title:
--   Prepending a long-range Kac attraction approximates the mean-field transform of the physical pressure near the initial point (OpenAI continuum temperature)
-- statement:
--   Notation, following OpenAI's definitions. For masses $\sigma : \mathbb N \to \mathbb R$ and ranges $R : \mathbb N \to \mathbb R$, the potential `physicalProfile t σ R` is $r \mapsto$ `coreProfile t r` $- \, t \sum_j \sigma_j\,$`scaledKernelProfile (R j) r`: OpenAI's core potential minus a sum of attractive Kac terms of strengths $\sigma_j$ and ranges $R_j$. `physicalPressure φ t (β, h)` $= \texttt{canonicalPressure}\ \varphi\ \beta\ (t h)/t$, the canonical pressure of $\varphi$ (the supremum over densities $d \ge 0$ of $\mu d$ minus the canonical free energy density `canonicalDensity φ β d`) at $\mu = t h$, divided by $t$. `meanField Q a (β, h)` $= \sup_{d} \bigl(Q(\beta, h + \beta a d) - \beta a d^2/2\bigr)$. Suprema are Lean's `sSup` on $\mathbb R$ ($0$ for a set not bounded above). `prepend a σ` is the sequence $a, \sigma_0, \sigma_1, \dots$, and `initialPoint` $= (1, -3/4)$. `ConstructionCap t M` says $1 < t$, $0 < M$, $140608 \cdot$ `kernelHeight` $\cdot M \le t$ and $1024\,M < t$.
--
--   **Statement.** Let $t, M, a$ be real numbers with `ConstructionCap t M` and $a > 0$. Let $\sigma, R : \mathbb N \to \mathbb R$ with $\sigma_n \ge 0$ and $R_n \ge 1$ for all $n$, $\sum_n \sigma_n$ convergent and $a + \sum_n \sigma_n \le M$. Let $R_0 \ge 0$ with $R_n \le R_0$ whenever $\sigma_n \ne 0$. Then for every $\varepsilon > 0$ and every $B \in \mathbb R$ there is $R_{\mathrm{new}} > \max(4, B)$ such that for every $x$ in the closed ball of radius $1/4$ about `initialPoint`,
--   $$\Bigl|\ \texttt{physicalPressure}\ \bigl(\texttt{physicalProfile}\ t\ (\texttt{prepend}\ a\ \sigma)\ (\texttt{prepend}\ R_{\mathrm{new}}\ R)\bigr)\ t\ x \;-\; \texttt{meanField}\ \bigl(\texttt{physicalPressure}\ (\texttt{physicalProfile}\ t\ \sigma\ R)\ t\bigr)\ a\ x\ \Bigr| \;\le\; \varepsilon.$$
--
--   Lean: `OAI.ContinuumTemperature.physical_kac_approximate`, OpenAI's lemma of that name (in `lean/OAI/Probability/ContinuumTransition/KacUniform.lean`). `physicalProfile`, `coreProfile`, `scaledKernelProfile`, `physicalPressure`, `canonicalPressure`, `canonicalDensity`, `meanField`, `prepend`, `initialPoint`, `ConstructionCap` and `kernelHeight` come from the definitions bundle `OAIQWCT000` of this split.
-- source:
--   OpenAI, A continuum temperature singularity for a radial pair potential, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 228; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-continuum-temperature-singularity-for-a-radial-pair-potential-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/ContinuumTransition/KacUniform.lean (declaration OAI.ContinuumTemperature.physical_kac_approximate)

import Mathlib
import Definitions.Def_OAIQWCT000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Topology
open Set Filter Metric
noncomputable section
namespace ContinuumTemperature

lemma physical_kac_approximate {t M a : ℝ} (hcap : ConstructionCap t M) (ha : 0 < a)
    {σ R : ℕ → ℝ} (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ)
    (hm : a+∑' n, σ n ≤ M) {R₀ : ℝ} (hR₀ : 0 ≤ R₀) (hbound : ∀ n, σ n ≠ 0 → R n ≤ R₀)
    {ε : ℝ} (hε : 0 < ε) (B : ℝ) :
    ∃ Rnew : ℝ, 4 < Rnew ∧ B < Rnew ∧
      ∀ x ∈ closedBall initialPoint (1/4),
        |physicalPressure (physicalProfile t (prepend a σ) (prepend Rnew R)) t x-
          meanField (physicalPressure (physicalProfile t σ R) t) a x| ≤ ε := by
  sorry

end ContinuumTemperature
end
end

end OAI
end
