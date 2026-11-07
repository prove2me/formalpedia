-- Prove2me | Theorems.Thm_LosslessQLTC_theorem_3_2
-- name    : LosslessQLTC.theorem_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:23:43.271264+00:00
-- url     : https://prove2.me/theorems/4b5fdfce-36d4-45aa-a0db-70021191e517
-- title:
--   Theorem 3.2, p.21 (corrected: lossless range for the link) — links of lossless complexes expand
-- statement:
--   Let $X$ be a $k$-dimensional lossless square complex with parameters $(D_i,D'_i,c_i,\varepsilon_i)_{i=1}^k$. Fix $I\subseteq[k]$ with $|I|<k$ and a vertex $v\in V_I$, and put $d=k-|I|$. Assume that $|\mathrm{Lk}_J(v)|\le c_j|V_{I\cup J}|$ for all $J\subseteq[k]\setminus I$ and all $j\notin I\cup J$. Then, for every $-1\le r\le d-2$ and every cochain $f:\mathrm{Lk}_r(v)\to\mathbb F_2$,
--
--   $$\|\delta_rf\|_v\ge m_{d,r}\operatorname{dist}(f)-O_k\Big(\sum_{j=1}^k\varepsilon_j\Big).$$
--
--   So links of a lossless complex inherit the expansion of a complete multipartite complex, up to an additive error depending on the loss.
--
--   Differences from the source:
--   - correction: Theorem 3.2 with no condition on the size of $\mathrm{Lk}_J(v)$ → the added hypothesis $|\mathrm{Lk}_J(v)|\le c_j|V_{I\cup J}|$ for $J\subseteq[k]\setminus I$, $j\notin I\cup J$; reason: the printed statement is false: the left-right Cayley complex of $\mathbb Z_2$ with $A=B=\mathbb Z_2$, $c_i=1/3$, any small $\varepsilon_i$, $I=\emptyset$, $r=0$, $f=1_{V_{\{1\}}}$ has $\delta f=0$, $\operatorname{dist}(f)=1$ and $m_{2,0}=1/6$; the printed proof applies expansion to exactly these sets at (3.4), and Theorem 4.10's use of it is in this range
--   - reading: $O_k(\cdot)$ in (3.2) → a constant $C>0$ depending only on $k$, chosen before the complex and the other data; reason: the proofs bound this error by a function of $k$ alone
--   - encoding: a decorated $(k,2)$-cubical complex with blocks $V_I$ and cubes $X(i)$ for all $i$, directions $1,\dots,k$ → `SquareComplex k`: one vertex type with a type map, the graph and $X(2)$ only, directions `Fin k`; reason: $X(0),X(1)$ are forced, no result uses $X(i)$ for $i\ge3$, and any such data extends with $X(i)=\emptyset$ for $i\ge3$
--   - encoding: link level $r$, with $-1\le r$ → index $j=r+1\in\mathbb N$, with $m_{d,r}$ as `mConst d j`; reason: avoids natural-number subtraction; same instances
-- source:
--   Cohen, Leigh, Reiner, Ta-Shma, Tzalik, Good Quantum Locally Testable Codes from Lossless Cubical Complexes, arXiv:2610.00525 (held version, sha256 d61f0ed9…), Theorem 3.2, p.21; correction from the proof, eq. (3.4), p.23, and p.27

import Mathlib
import Definitions.Def_LosslessQLTC_IsLossless
import Definitions.Def_LosslessQLTC_Link
import Definitions.Def_LosslessQLTC_mConst

namespace LosslessQLTC

/-- Theorem 3.2 (arXiv:2610.00525, held version, sha256 d61f0ed9…, p.21), corrected: let `X` be a
`k`-dimensional lossless square complex, `v ∈ V_I` with `|I| < k`, `d = k − |I|`. For every
`−1 ≤ r ≤ d − 2` and `f : Lk_r(v) → F₂`, `∥δ_r f∥_v ≥ m_{d,r} dist(f) − O_k(Σ_j ε_j)`, provided every
`Lk_J(v)` lies in the lossless range of each direction outside `I ∪ J`.

**Formalization Note.** The range hypothesis `hrange` is not printed. Without it the statement is
false: the left-right Cayley complex of `Z₂` with `A = B = Z₂`, `c_i = 1/3`, `I = ∅`, `r = 0`,
`f = 1_{V_{1}}` has `δf = 0`, `dist(f) = 1`, `m_{2,0} = 1/6`, while every `ε_i ∈ (0, 1)` is allowed.
The printed proof uses this range at (3.4), and the application in Theorem 4.10 is in range. `C`
depends only on `k`. `j = r + 1`, so `−1 ≤ r ≤ d − 2` is `j < d`. -/
theorem theorem_3_2 (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (X : SquareComplex k) (c ε : Fin k → ℝ), IsLossless X c ε →
      ∀ (v : X.Vtx) (d : ℕ), (X.type v).card + d = k →
        (∀ J : Finset (Fin k), Disjoint J (X.type v) → ∀ m, m ∉ X.type v ∪ J →
          ((LkType X v J).card : ℝ) ≤ c m * Fintype.card (Block X (X.type v ∪ J))) →
        ∀ (j : ℕ), j < d → ∀ f : LinkCochain X v j,
          mConst d j * distLink X v j f - C * epsStar ε ≤ linkNorm X v (deltaLink X v j f) := by sorry

end LosslessQLTC
