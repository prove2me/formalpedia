-- Prove2me | Theorems.Thm_OAI_ContinuumTemperature_core_pressure_locally_uniform
-- name    : OAI.ContinuumTemperature.core_pressure_locally_uniform
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T19:05:38.049477+00:00
-- url     : https://prove2.me/theorems/bee7c201-69d1-49d5-a560-4fe9155d1817
-- title:
--   As t → ∞ the physical pressure of the core profile converges locally uniformly to the ideal core pressure (OpenAI continuum temperature)
-- statement:
--   Notation, following the published bundle `Def_ContinuumTransition` and OpenAI's definitions. For a radial pair potential $\varphi : \mathbb R \to \mathbb R$, `partition φ β L N` is the canonical partition function of $N$ particles in the cube of side $L$ in $\mathbb R^3$ at inverse temperature $\beta$. Then:
--   - `finiteCanonical φ β L N` $= -\log(\texttt{partition}\ \varphi\ \beta\ L\ N)/L^3$;
--   - `canonicalDensity φ β d` is its $\liminf$ along `densityFilter d`, the filter along which $L \to \infty$ and $N/L^3 \to d$;
--   - `canonicalPressure φ β μ` $= \sup_{d \ge 0} \bigl(\mu d - \texttt{canonicalDensity}\ \varphi\ \beta\ d\bigr)$;
--   - `physicalPressure φ t (β, h)` $= \texttt{canonicalPressure}\ \varphi\ \beta\ (t h)/t$.
--
--   Suprema here are Lean's `sSup` on $\mathbb R$, which is $0$ for a set that is not bounded above. The core profile `coreProfile t` is the potential with value $t^2 + (e^{-t}/r)^{12}$ for $r < e^{-t}$, $0$ for $e^{-t} \le r \le (1 + 1/1000)\,e^{-t}$, $t^2$ for $(1 + 1/1000)\,e^{-t} < r < 1$, and $0$ for $r \ge 1$. Let $p$ be `packingDensity`, the supremum over $L \ge 0$ of `packingNumber L` $/(L+2)^3$, and let `idealCorePressure h` $= \max(0,\ p h,\ 4 p h - 9p)$.
--
--   **Statement.** As $t \to \infty$ (over the reals), the functions $(\beta, h) \mapsto$ `physicalPressure (coreProfile t) t (β, h)` converge to $(\beta, h) \mapsto$ `idealCorePressure h` locally uniformly on `pressureDomain` $= \{(\beta, h) \in \mathbb R \times \mathbb R : \beta > 0\}$ (Mathlib's `TendstoLocallyUniformlyOn`).
--
--   Lean: `OAI.ContinuumTemperature.core_pressure_locally_uniform`, OpenAI's theorem of that name (in `lean/OAI/Probability/ContinuumTransition/PhysicalUniform.lean`). `partition` comes from the published bundle `Def_ContinuumTransition`; `physicalPressure`, `canonicalPressure`, `canonicalDensity`, `finiteCanonical`, `densityFilter`, `coreProfile`, `packingDensity`, `packingNumber`, `idealCorePressure` and `pressureDomain` from the definitions bundle `OAIQWCT000` of this split.
-- source:
--   OpenAI, A continuum temperature singularity for a radial pair potential, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 228; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-continuum-temperature-singularity-for-a-radial-pair-potential-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/ContinuumTransition/PhysicalUniform.lean (declaration OAI.ContinuumTemperature.core_pressure_locally_uniform)

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
open Set Filter
namespace ContinuumTemperature

 theorem core_pressure_locally_uniform :
    TendstoLocallyUniformlyOn (fun t : ℝ => physicalPressure (coreProfile t) t)
      (fun x : Parameter => idealCorePressure x.2) atTop pressureDomain := by
  sorry

end ContinuumTemperature
end

end OAI
end
