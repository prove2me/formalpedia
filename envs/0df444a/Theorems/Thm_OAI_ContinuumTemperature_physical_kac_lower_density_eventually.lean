-- Prove2me | Theorems.Thm_OAI_ContinuumTemperature_physical_kac_lower_density_eventually
-- name    : OAI.ContinuumTemperature.physical_kac_lower_density_eventually
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T19:06:16.330698+00:00
-- url     : https://prove2.me/theorems/26d51576-d642-4131-8931-55338aa9d860
-- title:
--   Eventual lower bound on the physical pressure after prepending a long-range Kac attraction (OpenAI continuum temperature)
-- statement:
--   Notation, following OpenAI's definitions. `kernel` is OpenAI's radial kernel on $\mathbb R^3$, $x \mapsto b(x)/\int b$ with $b(x) = $ `Real.smoothTransition (2 - 2‖x‖)`, and `kernelHeight` $= 1/\int b$. For masses $\sigma$ and ranges $R$ (sequences $\mathbb N \to \mathbb R$), `physicalProfile t σ R` is the potential $r \mapsto$ `coreProfile t r` $- \, t \sum_j \sigma_j\,$`scaledKernelProfile (R j) r`. `canonicalDensity φ β d` is the canonical free energy density of the potential $\varphi$ at inverse temperature $\beta$ and density $d$ (the $\liminf$ of $-\log(\texttt{partition}\ \varphi\ \beta\ L\ N)/L^3$ as $L \to \infty$ with $N/L^3 \to d$), and `physicalPressure φ t (β, h)` $= \texttt{canonicalPressure}\ \varphi\ \beta\ (t h)/t$, where `canonicalPressure φ β μ` is the supremum (Lean's `sSup`) over $d \ge 0$ of $\mu d - $ `canonicalDensity φ β d`. `prepend a σ` is the sequence $a, \sigma_0, \sigma_1, \dots$.
--
--   **Statement.** Let $C \ge 0$ with `kernel` $C$-Lipschitz, and let $t, \beta, a$ be real numbers with $t > 1$, $\beta > 0$, $a \ge 0$. Let $\sigma, R : \mathbb N \to \mathbb R$ with $\sigma_n \ge 0$ and $R_n \ge 1$ for all $n$, $\sum_n \sigma_n$ convergent, and
--   $$2197\, t \cdot \texttt{kernelHeight} \cdot \Bigl(a + \sum_j \sigma_j\Bigr) \;\le\; \frac{t^2/8}{8}.$$
--   Let $h \in \mathbb R$, $d \ge 0$, and $c$ a real number with
--   $$c \;<\; \frac{t h d - \texttt{canonicalDensity}\ (\texttt{physicalProfile}\ t\ \sigma\ R)\ \beta\ d + \beta\,(t a)\,d^2/2}{t}.$$
--   Then for all sufficiently large natural numbers $q$,
--   $$c \;<\; \texttt{physicalPressure}\ \Bigl(\texttt{physicalProfile}\ t\ (\texttt{prepend}\ a\ \sigma)\ \bigl(\texttt{prepend}\ (q/4)^2\ R\bigr)\Bigr)\ t\ (\beta, h).$$
--
--   Lean: `OAI.ContinuumTemperature.physical_kac_lower_density_eventually`, OpenAI's theorem of that name (in `lean/OAI/Probability/ContinuumTransition/LowerKac.lean`). `partition` comes from the published bundle `Def_ContinuumTransition`; `kernel`, `kernelHeight`, `physicalProfile`, `coreProfile`, `scaledKernelProfile`, `canonicalDensity`, `canonicalPressure`, `physicalPressure` and `prepend` from the definitions bundle `OAIQWCT000` of this split.
-- source:
--   OpenAI, A continuum temperature singularity for a radial pair potential, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 228; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-continuum-temperature-singularity-for-a-radial-pair-potential-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/ContinuumTransition/LowerKac.lean (declaration OAI.ContinuumTemperature.physical_kac_lower_density_eventually)

import Mathlib
import Definitions.Def_ContinuumTransition
import Definitions.Def_OAIQWCT000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Topology BigOperators
open Filter
namespace ContinuumTemperature

theorem physical_kac_lower_density_eventually {C : NNReal} (hC : LipschitzWith C kernel)
    {t β a : ℝ} (ht : 1 < t) (hβ : 0 < β) (ha : 0 ≤ a)
    {σ R : ℕ → ℝ} (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ)
    (hsmall : 2197*t*kernelHeight*(a+∑' j, σ j) ≤ (t^2/8)/8)
    (h : ℝ) {d : ℝ} (hd : 0 ≤ d) {c : ℝ}
    (hc : c < (t*h*d-canonicalDensity (physicalProfile t σ R) β d+β*(t*a)/2*d^2)/t) :
    ∀ᶠ q : ℕ in atTop, c <
      physicalPressure (physicalProfile t (prepend a σ) (prepend (((q : ℝ)/4)^2) R)) t (β,h) := by
  sorry

end ContinuumTemperature
end

end OAI
end
