-- Prove2me | Theorems.Thm_LosslessQLTC_theorem_4_10
-- name    : LosslessQLTC.theorem_4_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:23:59.450566+00:00
-- url     : https://prove2.me/theorems/7f1d84f0-ad58-4db1-9e72-37ca3d0afffa
-- title:
--   Theorem 4.10, p.38 — small-set coboundary expansion of lossless imbalanced square complexes
-- statement:
--   Let $X$ be a lossless $k$-dimensional square complex with parameters $(D_i,D'_i,c_i,\varepsilon_i)_{i\in[k]}$, imbalanced so that (4.25) holds. For $0\le r\le k-1$, let $H_r:V_r\to\mathbb F_2$ be a locally minimal cochain, of norm at most $c\|V_r\|$, for $c$ as in (4.26). Then
--
--   $$\|\delta H_r\|\ge\big(m_{k,r-1}-O_k(\varepsilon_\star^{1/2^r})\big)\|H_r\|,$$
--
--   where the constant in $O_k$ depends only on $k$. This is the central combinatorial statement of the paper, and it holds at every level and in every dimension.
--
--   Differences from the source:
--   - reading: $O_k(\cdot)$ in the conclusion → a constant $C>0$ depending only on $k$, chosen before the complex and the other data; reason: the proofs bound this error by a function of $k$ alone
--   - encoding: a decorated $(k,2)$-cubical complex with blocks $V_I$ and cubes $X(i)$ for all $i$, directions $1,\dots,k$ → `SquareComplex k`: one vertex type with a type map, the graph and $X(2)$ only, directions `Fin k`; reason: $X(0),X(1)$ are forced, no result uses $X(i)$ for $i\ge3$, and any such data extends with $X(i)=\emptyset$ for $i\ge3$
--   - encoding: $m_{k,r-1}$ with $r\ge0$ → `mConst k r`; reason: avoids natural-number subtraction; same constant
-- source:
--   Cohen, Leigh, Reiner, Ta-Shma, Tzalik, Good Quantum Locally Testable Codes from Lossless Cubical Complexes, arXiv:2610.00525 (held version, sha256 d61f0ed9…), Theorem 4.10, p.38

import Mathlib
import Definitions.Def_LosslessQLTC_IsLossless
import Definitions.Def_LosslessQLTC_Link
import Definitions.Def_LosslessQLTC_mConst

namespace LosslessQLTC

/-- Theorem 4.10 (arXiv:2610.00525, held version, sha256 d61f0ed9…, p.38): let `X` be a lossless
`k`-dimensional square complex with (4.25). For `0 ≤ r ≤ k − 1`, let `H_r : V_r → F₂` be locally
minimal of norm at most `c ∥V_r∥`, with `c` as in (4.26). Then
`∥δH_r∥ ≥ (m_{k,r−1} − O_k(ε⋆^{1/2^r})) ∥H_r∥`.

**Formalization Note.** `O_k` is a constant `C` depending only on `k`, chosen before `X`, the
parameters and `r`. `m_{k,r−1}` is `mConst k r`. The exponent is a real power with `ε⋆ > 0`. -/
theorem theorem_4_10 (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (X : SquareComplex k) (c ε : Fin k → ℝ), IsLossless X c ε →
      IsImbalanced X ε → ∀ (r : ℕ), r < k → ∀ H : Level X r → ZMod 2, IsLocallyMinimal X r H →
        normC X H ≤ cConst X.D X.D' c * levelMass X r →
        (mConst k r - C * epsStar ε ^ ((1 : ℝ) / 2 ^ r)) * normC X H ≤
          normC X (delta X r H) := by sorry

end LosslessQLTC
