-- Prove2me | Theorems.Thm_OAI_Erdos3_fullSmoothPairError_nonneg
-- name    : OAI.Erdos3.fullSmoothPairError_nonneg
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T11:37:43.884039+00:00
-- url     : https://prove2.me/theorems/9c1bd37e-dd19-4c16-bdf7-2b3cc55f168f
-- title:
--   The full smooth pair error is nonnegative for nonnegative δ
-- statement:
--   Let $J$ be a finite type with decidable equality, let $n,Q\in\mathbb N$, $k\in J$, and $C,\kappa,\delta\in\mathbb R$ with $0\le\delta$ (no hypothesis is placed on $C$ or $\kappa$). Then $0\le$ `fullSmoothPairError n k Q C κ δ`. Here `fullSmoothPairError n k Q C κ δ` is the real number
--   $$n\cdot E\cdot(P+E)^n,\qquad E=\texttt{smoothPairProbabilityError}\ k\ Q\ C\ \kappa\ \delta,\quad P=\texttt{smoothPairProbabilityCap}\ k\ Q\ C\ \kappa,$$
--   where `smoothPairProbabilityCap k Q C κ` $=1+Q\cdot 2(4C/\kappa)^2\,2^{|\{j\in J:j\ne k\}|}$ and `smoothPairProbabilityError k Q C κ δ` is the constant `normalizedFiberErrorConstant 2 |{j : j ≠ k}| Q (4C/κ) (|J|·C) 1 1 (smoothPairRowLipschitz k)` multiplied by $\delta$.
--
--   Lean: `OAI.Erdos3.fullSmoothPairError_nonneg` in `lean/OAI/Combinatorics/Progressions/Estimates/SmoothPairErrorLogBounds.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B014` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/SmoothPairErrorLogBounds.lean#L160

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B014

namespace OAI

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem fullSmoothPairError_nonneg {J : Type*} [Fintype J] [DecidableEq J]
    (n : ℕ) (k : J) (Q : ℕ) (C κ δ : ℝ) (hδ : 0 ≤ δ) :
    0 ≤ fullSmoothPairError n k Q C κ δ := by
  sorry

end Erdos3
end
end OAI
