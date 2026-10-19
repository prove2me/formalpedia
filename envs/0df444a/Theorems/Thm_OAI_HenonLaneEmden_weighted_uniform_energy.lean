-- Prove2me | Theorems.Thm_OAI_HenonLaneEmden_weighted_uniform_energy
-- name    : OAI.HenonLaneEmden.weighted_uniform_energy
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-19T01:39:31.285208+00:00
-- url     : https://prove2.me/theorems/3e0087ad-188d-4430-88f3-39fb91ec82a4
-- title:
--   Uniform local energy bound for positive entire solutions of the subcritical Hénon–Lane–Emden system (OpenAI Hénon–Lane–Emden theorem)
-- statement:
--   `Space n`, `IsSolution` and `Subcritical` are the definitions of the published bundle `Def_HenonEmden`: `Space n` is $\mathbb R^n$ (`EuclideanSpace ℝ (Fin n)`), `Subcritical n p q A B` is $\frac{n+A}{p+1} + \frac{n+B}{q+1} > n-2$, and `IsSolution n p q A B u v` says that $u, v$ are continuous and positive on $\mathbb R^n$, $C^2$ on $\mathbb R^n \setminus \{0\}$, and satisfy $-\Delta u = |x|^A v^p$, $-\Delta v = |x|^B u^q$ there. The other definitions are from the definitions bundle `OAIQWHLE000`: `source u q B` is $f(x) = |x|^B u(x)^q$ (with $f(0) = 0$), `eta n` is OpenAI's cutoff $\eta(x) = [(1 - (|x|-1)_+^3)_+]^N$ (equal to $1$ on the unit ball, supported in the ball of radius $2$), and `weightedEnergy χ u q B` is $\int \chi\, f\, u$.
--
--   **Statement.** Let $n \ge 3$, $p, q > 0$ and $A, B \in \mathbb R$ with `Subcritical n p q A B`. There is a constant $C \ge 0$ such that every solution $(u, v)$ satisfies
--   $$E_f + E_g \;=\; \int \eta\, |x|^B u^{q+1} + \int \eta\, |x|^A v^{p+1} \;\le\; C,$$
--   where $E_f$ = `weightedEnergy (eta n) u q B` and $E_g$ = `weightedEnergy (eta n) v p A`.
--
--   This is Proposition 6.1 of the paper: the localized energy is bounded independently of the solution. Since the system is invariant under the dilations $u \mapsto R^\alpha u(R\,\cdot)$, $v \mapsto R^\beta v(R\,\cdot)$ while the unit-ball energy scales by $R^{\alpha+\beta+2-n}$ with a positive exponent in the subcritical range, the bound yields the nonexistence theorem.
--
--   Lean: `OAI.HenonLaneEmden.weighted_uniform_energy`, OpenAI's theorem of that name (in `lean/OAI/Analysis/HenonEmden/UniformEnergy.lean`). It is published as an intermediate statement of this split because the single-file proof takes longer than the platform's verifier allows.
-- source:
--   OpenAI, The Subcritical Hénon–Lane–Emden Conjecture, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 370; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Subcritical-Henon-Lane-Emden-Conjecture-September-24-2026/paper.pdf, Proposition 6.1; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/HenonEmden/UniformEnergy.lean (declaration OAI.HenonLaneEmden.weighted_uniform_energy)

import Mathlib
import Definitions.Def_HenonEmden
import Definitions.Def_OAIQWHLE000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section UniformEnergy

open MeasureTheory Set Metric
open scoped ENNReal
noncomputable section
namespace HenonLaneEmden
open Cutoff

lemma weighted_uniform_energy {n : ℕ} (hn : 3 ≤ n) {p q A B : ℝ} (hp : 0 < p) (hq : 0 < q)
    (hsub : Subcritical n p q A B) : ∃ C : ℝ, 0 ≤ C ∧
      ∀ u v : Space n → ℝ, IsSolution n p q A B u v →
        weightedEnergy (eta n) u q B+weightedEnergy (eta n) v p A ≤ C := by
  sorry

end HenonLaneEmden
end
end UniformEnergy

end OAI
end
