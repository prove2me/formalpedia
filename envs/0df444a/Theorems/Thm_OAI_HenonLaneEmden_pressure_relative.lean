-- Prove2me | Theorems.Thm_OAI_HenonLaneEmden_pressure_relative
-- name    : OAI.HenonLaneEmden.pressure_relative
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-19T01:39:54.244347+00:00
-- url     : https://prove2.me/theorems/69421ebc-c1f7-4840-91af-98fbba9b3236
-- title:
--   Localized pressure estimate for the Hénon–Lane–Emden system: the weighted energies are controlled by the radial pressure up to a small multiple of the energy (OpenAI Hénon–Lane–Emden theorem)
-- statement:
--   `Space n` and `IsSolution` are the definitions of the published bundle `Def_HenonEmden` ($\mathbb R^n$, and positive solutions of $-\Delta u = |x|^A v^p$, $-\Delta v = |x|^B u^q$ off the origin, continuous at it). The other definitions are from the definitions bundle `OAIQWHLE000`: `source u q B` is $f = |x|^B u^q$, `eta n` is the cutoff $\eta$ and `w n` is $w(x) = -x\cdot\nabla\eta(x)$, `weightedEnergy χ u q B` is $\int \chi f u$, and `radialPressure f g` is $(n-2)\int w(x)\,D(x,y)\,d\pi(x,y)$, where $d\pi = f(x)g(y)K(x-y)\,dx\,dy$ is the interaction measure (`interaction`) with the Newton kernel $K$ and $D$ = `radialFactor` is $\frac{(x\cdot(x-y))^2}{|x|^2|x-y|^2}$.
--
--   **Statement.** Let $n \ge 3$, $p, q > 0$, $A, B \in \mathbb R$ and $\varepsilon > 0$. There is a constant $C \ge 0$ such that every solution $(u, v)$ satisfies, with $f$ = `source u q B` and $g$ = `source v p A`,
--   $$\frac{W_f}{q+1} + \frac{W_g}{p+1} - (n-2)\!\int w(x)D(x,y)\,d\pi \;\le\; \varepsilon\,(E_f + E_g) + C,$$
--   where $W_f$ = `weightedEnergy (w n) u q B`, $W_g$ = `weightedEnergy (w n) v p A`, $E_f$ = `weightedEnergy (eta n) u q B` and $E_g$ = `weightedEnergy (eta n) v p A`.
--
--   This is Proposition 5.1 of the paper (localized pressure).
--
--   Lean: `OAI.HenonLaneEmden.pressure_relative`, OpenAI's theorem of that name (in `lean/OAI/Analysis/HenonEmden/RelativePressure.lean`). It is published as an intermediate statement of this split because the single-file proof takes longer than the platform's verifier allows.
-- source:
--   OpenAI, The Subcritical Hénon–Lane–Emden Conjecture, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 370; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Subcritical-Henon-Lane-Emden-Conjecture-September-24-2026/paper.pdf, Proposition 5.1; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/HenonEmden/RelativePressure.lean (declaration OAI.HenonLaneEmden.pressure_relative)

import Mathlib
import Definitions.Def_HenonEmden
import Definitions.Def_OAIQWHLE000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section RelativePressure

open MeasureTheory Set Metric
noncomputable section
namespace HenonLaneEmden
open Cutoff

lemma pressure_relative {n : ℕ} (hn : 3 ≤ n) {p q A B ε : ℝ} (hp : 0 < p) (hq : 0 < q)
    (hε : 0 < ε) : ∃ C : ℝ, 0 ≤ C ∧ ∀ u v : Space n → ℝ, IsSolution n p q A B u v →
      (q+1)⁻¹*weightedEnergy (w n) u q B+(p+1)⁻¹*weightedEnergy (w n) v p A-
        radialPressure (source u q B) (source v p A) ≤
        ε*(weightedEnergy (eta n) u q B+weightedEnergy (eta n) v p A)+C := by
  sorry

end HenonLaneEmden
end
end RelativePressure

end OAI
end
