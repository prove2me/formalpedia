-- Prove2me | Theorems.Thm_OAI_ContinuumTemperature_core_transform_locally_uniform
-- name    : OAI.ContinuumTemperature.core_transform_locally_uniform
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T19:05:29.371817+00:00
-- url     : https://prove2.me/theorems/ae9843ce-87c3-41bc-aa8a-62507ba3f0f9
-- title:
--   Near the initial point, the mean-field transforms of the core pressures converge locally uniformly to the three-branch mean field (OpenAI continuum temperature)
-- statement:
--   Notation, following OpenAI's definitions. `physicalPressure φ t (β, h)` $= \texttt{canonicalPressure}\ \varphi\ \beta\ (t h)/t$, where `canonicalPressure φ β μ` is the supremum over densities $d \ge 0$ of $\mu d$ minus the canonical free energy density `canonicalDensity φ β d` of the potential $\varphi$ (the $\liminf$ of $-\log(\texttt{partition}\ \varphi\ \beta\ L\ N)/L^3$ as $L \to \infty$ with $N/L^3 \to d$). `coreProfile t` is OpenAI's core potential (value $t^2 + (e^{-t}/r)^{12}$ for $r < e^{-t}$, $0$ for $e^{-t} \le r \le (1 + 1/1000)\,e^{-t}$, $t^2$ for $(1 + 1/1000)\,e^{-t} < r < 1$, $0$ for $r \ge 1$). For $Q : \mathbb R \times \mathbb R \to \mathbb R$, $a \in \mathbb R$ and $x = (\beta, h)$, the mean-field transform is
--   $$\texttt{meanField}\ Q\ a\ (\beta, h) \;=\; \sup_{d \in \mathbb R} \Bigl( Q(\beta,\ h + \beta a d) - \frac{\beta a d^2}{2} \Bigr),$$
--   and `threeMeanField p a (β, h)` $= \max\bigl(0,\ p h + \beta a p^2/2,\ 4 p h - 9p + \beta a (4p)^2/2\bigr)$. Suprema here are Lean's `sSup` on $\mathbb R$, which is $0$ for a set that is not bounded above. Let $p$ be `packingDensity` (the supremum over $L \ge 0$ of `packingNumber L` $/(L+2)^3$) and `initialPoint` $= (1, -3/4)$.
--
--   **Statement.** Let $T, a$ be real numbers with $T > 1$, $a > 0$ and $1024\,a < T$. As $n \to \infty$ over the natural numbers, the functions
--   $$x \mapsto \texttt{meanField}\ \bigl(\texttt{physicalPressure}\ (\texttt{coreProfile}\ (n + T))\ (n + T)\bigr)\ a\ x$$
--   converge to $x \mapsto$ `threeMeanField p a x` locally uniformly on the open ball of radius $1/2$ about `initialPoint` in $\mathbb R \times \mathbb R$ (with its product metric, the maximum of the coordinate distances).
--
--   Lean: `OAI.ContinuumTemperature.core_transform_locally_uniform`, OpenAI's lemma of that name (in `lean/OAI/Probability/ContinuumTransition/InitialUniform.lean`). `partition` comes from the published bundle `Def_ContinuumTransition`; `meanField`, `threeMeanField`, `physicalPressure`, `canonicalPressure`, `canonicalDensity`, `coreProfile`, `packingDensity` and `initialPoint` from the definitions bundle `OAIQWCT000` of this split.
-- source:
--   OpenAI, A continuum temperature singularity for a radial pair potential, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 228; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-continuum-temperature-singularity-for-a-radial-pair-potential-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/ContinuumTransition/InitialUniform.lean (declaration OAI.ContinuumTemperature.core_transform_locally_uniform)

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

lemma core_transform_locally_uniform {T a : ℝ} (hT : 1 < T) (ha : 0 < a) (hTa : 1024*a < T) :
    TendstoLocallyUniformlyOn
      (fun n : ℕ => meanField (physicalPressure (coreProfile ((n:ℝ)+T)) ((n:ℝ)+T)) a)
      (threeMeanField packingDensity a) atTop (ball initialPoint (1/2)) := by
  sorry

end ContinuumTemperature
end
end

end OAI
end
