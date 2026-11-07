-- Prove2me | Theorems.Thm_LosslessQLTC_theorem_3_8
-- name    : LosslessQLTC.theorem_3_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:20:27.930863+00:00
-- url     : https://prove2.me/theorems/33531cd5-3269-42a8-b064-3c09ab3bd114
-- title:
--   Theorem 3.8, p.25 — expansion of the link when its top part is almost full
-- statement:
--   Let $X$ be a $k$-dimensional square complex and let $v\in V_\emptyset$. Fix $0\le r\le k-2$. If $\|\mathrm{Lk}_{[k]}(v)\|\ge1-\eta$, then every cochain $f_r:\mathrm{Lk}_r(v)\to\mathbb F_2$ satisfies
--
--   $$\|\delta f_r\|\ge m_{k,r}\operatorname{dist}(f_r)-O_k(\eta),$$
--
--   where the constant in $O_k$ depends only on $k$. No lossless hypothesis appears: the size of the top of the link is the only input.
--
--   Differences from the source:
--   - encoding: a decorated $(k,2)$-cubical complex with blocks $V_I$ and cubes $X(i)$ for all $i$, directions $1,\dots,k$ → `SquareComplex k`: one vertex type with a type map, the graph and $X(2)$ only, directions `Fin k`; reason: $X(0),X(1)$ are forced, no result uses $X(i)$ for $i\ge3$, and any such data extends with $X(i)=\emptyset$ for $i\ge3$
--   - reading: $O_k(\cdot)$ in (3.7) → a constant $C>0$ depending only on $k$, chosen before the complex and the other data; reason: the proofs bound this error by a function of $k$ alone
--   - encoding: link level $r$, with $-1\le r$ → index $j=r+1\in\mathbb N$, with $m_{d,r}$ as `mConst d j`; reason: avoids natural-number subtraction; same instances
-- source:
--   Cohen, Leigh, Reiner, Ta-Shma, Tzalik, Good Quantum Locally Testable Codes from Lossless Cubical Complexes, arXiv:2610.00525 (held version, sha256 d61f0ed9…), Theorem 3.8, p.25

import Mathlib
import Definitions.Def_LosslessQLTC_Link
import Definitions.Def_LosslessQLTC_mConst

namespace LosslessQLTC

/-- Theorem 3.8 (arXiv:2610.00525, held version, sha256 d61f0ed9…, p.25): let `X` be a
`k`-dimensional square complex, `v ∈ V_∅`, and `0 ≤ r ≤ k − 2`. If `∥Lk_{[k]}(v)∥ ≥ 1 − η` then
every `f_r : Lk_r(v) → F₂` satisfies `∥δf_r∥ ≥ m_{k,r} dist(f_r) − O_k(η)`.

**Formalization Note.** `O_k` is a constant `C` depending only on `k`, chosen before `X`, `v`, `r`,
`η`. `j = r + 1`, so `0 ≤ r ≤ k − 2` is `1 ≤ j` and `j + 1 ≤ k`. For `v ∈ V_∅` the norm on `Lk(v)` is
the ambient norm, since `D_∅ = 1`. -/
theorem theorem_3_8 (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (X : SquareComplex k) (v : X.Vtx), X.type v = ∅ →
      ∀ (j : ℕ), 1 ≤ j → j + 1 ≤ k → ∀ η : ℝ,
        1 - η ≤ setNorm X (LkType X v Finset.univ) →
        ∀ f : LinkCochain X v j,
          mConst k j * distLink X v j f - C * η ≤ linkNorm X v (deltaLink X v j f) := by sorry

end LosslessQLTC
