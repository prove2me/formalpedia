-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_exists_preparedScalarStructuralBasePower
-- name    : OAI.Erdos3.VectorPolynomial.exists_preparedScalarStructuralBasePower
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-16T01:51:55.280015+00:00
-- url     : https://prove2.me/theorems/6630e59f-1fb2-417b-ba40-b16e5453f683
-- title:
--   A base power beyond which (p+2)^power dominates the scalar structural constants
-- statement:
--   For every natural number $s$ there is a natural number $\mathrm{baseMin} \ge 1$ such that for every natural number $\mathrm{basePower} \ge \mathrm{baseMin}$ and every real $p \ge 2$, writing $B = (p+2)^{\mathrm{basePower}}$, all of the following hold: $\texttt{scalarNativeDimension}\ s \le B$, where `scalarNativeDimension s` $= (s+1)(s+3)$; $\texttt{probabilityProfileLipschitz} \le e^{B}$; $\texttt{normalizedSiteCutoffBound} \le e^{B}$; and $p \le B$. Here `probabilityProfileLipschitz` is a fixed constant in $\mathbb R_{\ge 0}$ chosen by OpenAI as a Lipschitz constant, at least $1$, of OpenAI's `smoothProbabilityProfile`, and `normalizedSiteCutoffBound` is a fixed constant in $\mathbb R_{\ge 0}$ chosen by OpenAI as the Lipschitz constant, at least $1$, of a smooth cutoff $\chi : \mathbb R \to [0,1]$ equal to $1$ on $|x| \le 1/2$ and to $0$ on $|x| \ge 3/4$.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.exists_preparedScalarStructuralBasePower` in `lean/OAI/Combinatorics/Progressions/Estimates/PreparedScalarStructuralBasePower.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B1324` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/PreparedScalarStructuralBasePower.lean#L276

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B1324

namespace OAI

section

namespace Erdos3

open scoped NNReal ContDiff

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

end Erdos3

end

section

namespace Erdos3

open scoped NNReal ContDiff

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

theorem exists_preparedScalarStructuralBasePower (s : ℕ) :
    ∃ baseMin : ℕ, 1 ≤ baseMin ∧
      ∀ basePower : ℕ, baseMin ≤ basePower → ∀ p : ℝ, 2 ≤ p →
        let B := (p + 2) ^ basePower
        (scalarNativeDimension s : ℝ) ≤ B ∧
          (probabilityProfileLipschitz : ℝ) ≤ Real.exp B ∧
          (normalizedSiteCutoffBound : ℝ) ≤ Real.exp B ∧ p ≤ B := by
  sorry

end Erdos3.VectorPolynomial
end
end OAI
