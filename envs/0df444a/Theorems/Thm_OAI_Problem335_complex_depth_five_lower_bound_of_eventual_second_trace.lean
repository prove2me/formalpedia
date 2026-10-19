-- Prove2me | Theorems.Thm_OAI_Problem335_complex_depth_five_lower_bound_of_eventual_second_trace
-- name    : OAI.Problem335.complex_depth_five_lower_bound_of_eventual_second_trace
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-19T02:49:03.537521+00:00
-- url     : https://prove2.me/theorems/1e5096ad-21c9-4f4a-b7ab-73034afd102f
-- title:
--   A second-trace bound for the normalized IMM matrix implies the n^(√n/400) lower bound for homogeneous depth-five complex circuits (OpenAI depth five)
-- statement:
--   **IMM and circuits.** Let $\mathrm{IMM}_n$ (`imm ℂ n`) be the $(0,0)$ entry of the product $X_0 X_1 \cdots X_{n-1}$ of $n$ matrices of size $n \times n$ whose entries are independent variables $x_{t,i,j}$, a polynomial in `MvPolynomial (Fin n × Fin n × Fin n) ℂ`. A `Depth5Circuit ℂ n` is a syntactically homogeneous $\Sigma\Pi\Sigma\Pi\Sigma$ circuit:
--   - its leaves are scalars or variables;
--   - bottom gates are linear combinations of leaves, lower gates products of bottom gates, middle gates linear combinations of lower gates, and upper gates products of middle gates;
--   - the output is a linear combination of upper gates, and every summand of a sum gate has the gate's degree.
--
--   `circuitValue c` is the polynomial it computes, and `circuitSize c` the total number of its gates.
--
--   **The parameters.** For $n$ let $s = s(n)$ be $\lfloor\sqrt n\rfloor$ or $\lfloor\sqrt n\rfloor - 1$, whichever has the parity of $n$. Let $k = (n - s)/2$ and $m = (n + s)/2$, and put $v = kn^2$, $u = mn^2$ and $\rho = k/m$. Let
--   $$a = \Bigl\lceil \tfrac{v}{\sqrt n - 1} \Bigr\rceil, \qquad \alpha = \tfrac{a}{a + v}, \qquad b = \Bigl\lceil \tfrac{u\,\alpha^\rho}{1 - \alpha^\rho} \Bigr\rceil$$
--   (`LowerParameters.s`, `k`, `m`, `v`, `u`, `rho`, `a`, `alpha`, `b`). For $n \ge 4$ the balanced split `balancedLayer` marks $k$ of the $n$ matrix layers as derivative layers and the other $m$ as multiplication layers, following the balanced schedule `balancedWord`.
--
--   The normalized IMM matrix $M_n$ (`immNormalizedMatrix n (balancedLayer _) a b`) is the matrix of the following linear map, written in the factorial-normalized monomial bases of both spaces (`bidegreeComplexFockBasis`). Grade the variables by the layer they belong to. The map `finiteMixedOperator` that $\mathrm{IMM}_n$ induces goes from polynomials of bidegree $(a, b)$ to polynomials of bidegree $(a - k, b + m)$.
--
--   The normalizing quantities are
--   $$R_n = \binom{v + a - 1}{a}\binom{u + b - 1}{b} \ (\texttt{rankDimension}), \qquad S_n = n^{\,n-1}\Bigl(\frac{a}{v}\Bigr)^{k}\Bigl(1 + \frac{b}{u}\Bigr)^{m} \ (\texttt{rankMomentScale}).$$
--
--   **The statement.** Let $C$ be a real number, and suppose that for all large $n$ (with $n \ge 16$)
--   $$\operatorname{Re}\operatorname{tr}\bigl((M_n^* M_n)^2\bigr) \;\le\; R_n\, S_n^2\, e^{C\sqrt n}.$$
--   Then there is an $n_0$ such that every homogeneous depth-five circuit $c$ over $\mathbb C$ computing $\mathrm{IMM}_n$ with $n \ge n_0$ has
--   $$n^{\sqrt n/400} \;\le\; \mathrm{circuitSize}(c).$$
--
--   Lean: `OAI.Problem335.complex_depth_five_lower_bound_of_eventual_second_trace`, OpenAI's theorem of that name (in `lean/OAI/Algebra/DepthFive/LowerBoundAssembly.lean`). `Depth5Circuit`, `circuitValue`, `circuitSize` and `imm` come from the published bundle `Def_DepthFive`. `immNormalizedMatrix`, `balancedLayer`, `LowerParameters.rankDimension`, `LowerParameters.rankMomentScale`, `LowerParameters.a` and `LowerParameters.b` come from the definitions bundle `OAIQWDF000` of this split.
-- source:
--   OpenAI, Homogeneous depth-five lower bounds for iterated matrix multiplication, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 135; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Homogeneous-depth-five-lower-bounds-for-iterated-matrix-multiplication-September-25-2026/Homogeneous-depth-five-lower-bounds-for-iterated-matrix-multiplication-September-25-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/DepthFive/LowerBoundAssembly.lean (declaration OAI.Problem335.complex_depth_five_lower_bound_of_eventual_second_trace)

import Mathlib
import Definitions.Def_DepthFive
import Definitions.Def_OAIQWDF000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem335

open LowerParameters

theorem complex_depth_five_lower_bound_of_eventual_second_trace (C : ℝ)
    (hsecond : ∀ᶠ n : ℕ in Filter.atTop, ∀ hn : 16 ≤ n,
      (((immNormalizedMatrix n
          (balancedLayer (Nat.le_trans (by decide : 4 ≤ 16) hn)) (a n) (b n)).conjTranspose *
        immNormalizedMatrix n
          (balancedLayer (Nat.le_trans (by decide : 4 ≤ 16) hn)) (a n) (b n)) ^ 2).trace.re ≤
        rankDimension n * rankMomentScale n ^ 2 *
          Real.exp (C * Real.sqrt (n : ℝ))) :
    ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ c : Depth5Circuit ℂ n,
      circuitValue c = imm ℂ n →
      (n : ℝ) ^ (Real.sqrt (n : ℝ) / 400) ≤ (circuitSize c : ℝ) := by
  sorry

end Problem335

end

end OAI
end
