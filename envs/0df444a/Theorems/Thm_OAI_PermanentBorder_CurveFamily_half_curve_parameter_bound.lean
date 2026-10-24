-- Prove2me | Theorems.Thm_OAI_PermanentBorder_CurveFamily_half_curve_parameter_bound
-- name    : OAI.PermanentBorder.CurveFamily.half_curve_parameter_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-23T19:57:11.157428+00:00
-- url     : https://prove2.me/theorems/a74399eb-2a7e-4a9e-a1f1-47ae1661a7da
-- title:
--   A transcendence-degree and length bound for plane curves a² + xb² + yc² + xyd² in characteristic two (OpenAI permanent)
-- statement:
--   **Notation** (definitions bundle `OAIQWPB000` of this split). For $a, b, c, d \in L[x, y]$, the square form is $F = a^2 + x b^2 + y c^2 + xy d^2$ (`squareForm`), the half ideal is $(a, b, c, d)$ (`halfIdeal`), and the singular ideal of $F$ is $(F, \partial_x F, \partial_y F)$ (`singularIdeal`). $F_k$ denotes the degree-$k$ homogeneous component of $F$. A polynomial is in a subfield $E$ (`CurveFamily.InField E p`) when all its coefficients lie in $E$.
--
--   **The statement.** Let $K \subseteq L$ be fields of characteristic $2$, $K$ infinite and perfect, $L$ algebraically closed, and $k \ge 4$. Let $a, b, c, d \in L[x, y]$ with $\deg F \le k$, and suppose:
--   - $F_k$ is nonzero and squarefree;
--   - $\partial_y F_k \ne 0$ and $F_k$ is relatively prime to $\partial_y F_k$;
--   - $F_k$ is the image of a degree-$k$ homogeneous $H \in K[x, y]$;
--   - the zero locus of the singular ideal in $L^2$ is finite.
--
--   Then there are an intermediate field $K \subseteq E \subseteq L$ containing the coefficients of $F$ and $n$ with $\mathrm{trdeg}_K E \le n$ and
--   $$18n + 5\,\dim_L L[x,y]/(a,b,c,d) + \#\{z \in L^2 : z \text{ singular for } F,\ d(z) \ne 0\} \;\le\; 9k(k+1).$$
--
--   Lean: `OAI.PermanentBorder.CurveFamily.half_curve_parameter_bound`, OpenAI's theorem of that name (in `lean/OAI/Algebra/Determinantal/ConductorDimension.lean`).
-- source:
--   OpenAI, A cubic lower bound for border determinantal complexity of the permanent, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 108; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-cubic-lower-bound-for-border-determinantal-complexity-of-the-permanent-September-24-2026/A-cubic-lower-bound-for-border-determinantal-complexity-of-the-permanent-September-24-2026.pdf, Sections 4–5; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/Determinantal/ConductorDimension.lean (declaration OAI.PermanentBorder.CurveFamily.half_curve_parameter_bound)

import Mathlib
import Definitions.Def_OAIQWPB000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PermanentBorder.CurveFamily
open MvPolynomial Module LowPlane PlaneHilbert FrobeniusPlane
open scoped Classical
universe u
variable {K L : Type u} [Field K] [Field L] [Algebra K L] [CharP L 2]

variable [CharP K 2] [PerfectRing K 2] [Infinite K] [IsAlgClosed L]

theorem half_curve_parameter_bound {a b c d : Plane L} {k : ℕ}
    (hk : 4 ≤ k) (hf : (squareForm a b c d).totalDegree ≤ k)
    (hs : Squarefree (homogeneousComponent k (squareForm a b c d)))
    (hlead : homogeneousComponent k (squareForm a b c d) ≠ 0)
    (hpartial : pderiv 1 (homogeneousComponent k (squareForm a b c d)) ≠ 0)
    (hcop : IsRelPrime (homogeneousComponent k (squareForm a b c d))
      (pderiv 1 (homogeneousComponent k (squareForm a b c d))))
    (H : Plane K) (hH : H.IsHomogeneous k)
    (he : homogeneousComponent k (squareForm a b c d)=H.map (algebraMap K L))
    [Fintype (zeroLocus L (singularIdeal (squareForm a b c d)))] :
    ∃ (E : IntermediateField K L) (n : ℕ), InField E (squareForm a b c d) ∧
      Algebra.trdeg K E ≤ (n : Cardinal) ∧
      18*n+5*finrank L (Plane L ⧸ halfIdeal a b c d) +
        Fintype.card {x : zeroLocus L (singularIdeal (squareForm a b c d)) // eval x.val d≠0} ≤
          9*(k*(k+1)) := by
  sorry

end PermanentBorder.CurveFamily

end OAI
end
