-- Prove2me | Theorems.Thm_OAI_PermanentBorder_HasBorderDeterminant_coefficientPolynomial
-- name    : OAI.PermanentBorder.HasBorderDeterminant.coefficientPolynomial
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-23T19:56:44.891932+00:00
-- url     : https://prove2.me/theorems/fbb2f491-5424-4527-8a2a-d8c03e895280
-- title:
--   A border determinantal representation of the permanent restricts to one of the selected coefficient polynomial (OpenAI permanent, cf. Proposition 3.1)
-- statement:
--   **The selected coefficient** (definitions bundle `OAIQWPB000` of this split). For $k$, $q$ and $\theta \in \mathbb C^k$, `coefficientPolynomial k q θ` is $G_\theta(X) = [s^q t^q]\ \mathrm{per}_k(X + sI + tD)$ with $D = \mathrm{diag}(\theta_1, \dots, \theta_k)$: the coefficient of $s^q t^q$ in the permanent of the $k \times k$ matrix with entries $X_{ij}$ plus $s + \theta_i t$ on the diagonal, a polynomial in the $k^2$ variables $X_{ij}$ (`Selector.diagonalCoefficient`).
--
--   **The statement.** If the $m \times m$ permanent has a border determinantal representation of size $n$, then for all $q \le k$ with $11k - 2q \le m$ and every $\theta \in \mathbb C^k$, the polynomial $G_\theta$ has a border determinantal representation of the same size $n$.
--
--   This is the Lean consequence of the paper's Proposition 3.1 (coefficient projection: $G_\theta$ is, up to a nonzero constant, an affine projection of $\mathrm{per}_m$).
--
--   Lean: `OAI.PermanentBorder.HasBorderDeterminant.coefficientPolynomial`, OpenAI's theorem of that name (in `lean/OAI/Algebra/Determinantal/AffineSelectors.lean`).
-- source:
--   OpenAI, A cubic lower bound for border determinantal complexity of the permanent, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 108; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-cubic-lower-bound-for-border-determinantal-complexity-of-the-permanent-September-24-2026/A-cubic-lower-bound-for-border-determinantal-complexity-of-the-permanent-September-24-2026.pdf, cf. Proposition 3.1; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/Determinantal/AffineSelectors.lean (declaration OAI.PermanentBorder.HasBorderDeterminant.coefficientPolynomial)

import Mathlib
import Definitions.Def_PermanentCubic
import Definitions.Def_OAIQWPB000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PermanentBorder
open MvPolynomial

 theorem HasBorderDeterminant.coefficientPolynomial {k q m n : ℕ}
    (h : HasBorderDeterminant n (permanentPolynomial m)) (hq : q ≤ k)
    (hm : 11*k-2*q ≤ m) (θ : Fin k → ℂ) :
    HasBorderDeterminant n (coefficientPolynomial k q θ) := by
  sorry
end PermanentBorder

end OAI
end
