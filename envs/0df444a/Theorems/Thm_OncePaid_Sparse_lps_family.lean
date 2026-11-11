-- Prove2me | Theorems.Thm_OncePaid_Sparse_lps_family
-- name    : OncePaid.Sparse.lps_family
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T13:48:51.764202+00:00
-- url     : https://prove2.me/theorems/915757d1-db1c-40bd-a7a7-f49c1afb2027
-- title:
--   §A.3, LPS family — for primes $\ell\equiv305\ (\mathrm{mod}\ 404)$, $X_{101,\ell}$ is connected, bipartite, $102$-regular, with nontrivial singular values $\le2\sqrt{101}<21$
-- statement:
--   Let $\ell$ be a prime with $\ell\equiv305\pmod{404}$ and $i\in\mathbb F_\ell$ with $i^2=-1$. Then:
--
--   1. $\ell\equiv1\pmod4$ and $\ell\equiv2\pmod{101}$; $101$ is not a square modulo $\ell$, and $2$ is not a square modulo $101$ (so $(101/\ell)=(2/101)=-1$);
--   2. $|\mathrm{PGL}(2,\mathbb F_\ell)|=\ell(\ell^2-1)$ and the LPS graph $X_{101,\ell}$ is connected;
--   3. $X_{101,\ell}$ is bipartite between the square-determinant class and its complement (every edge joins the two classes), and each class has $\ell(\ell^2-1)/2$ elements;
--   4. every vertex has exactly $102$ neighbours, and the host $H_\ell$ between the two classes is $102$-regular;
--   5. all nontrivial biadjacency singular values of $H_\ell$ are at most $2\sqrt{101}$, i.e. $\|Bf\|_2\le2\sqrt{101}\,\|f\|_2$ for every $f$ on the non-square class with $\sum f=0$; and
--
--   $$
--   2\sqrt{101}\ <\ 21 .
--   $$
--
--   These are the facts the paper cites from Lubotzky–Phillips–Sarnak and Davidoff–Sarnak–Valette to realize Theorem 4.1's hypotheses for the explicit family $H_\ell$ with $n=\ell(\ell^2-1)/2$.
--
--   Differences from the source:
--   - generalization: "selecting the bipartite branch for all sufficiently large such primes" → every prime $\ell\equiv305\pmod{404}$; reason: the stronger statement specializes to the source's; every such prime is at least $709$, beyond the LPS size condition $\ell>2\sqrt{101}$.
--   - encoding: "simple connected bipartite 102-regular graph on $\ell(\ell^2-1)$ vertices" → a `SimpleGraph` on $\mathrm{PGL}(2,\mathbb F_\ell)$ with the listed properties, bipartition given by the determinant classes; Legendre symbols → non-squareness; nontrivial singular values $\le 2\sqrt{101}$ → $\|Bf\|_2^2\le(2\sqrt{101})^2\|f\|_2^2$ for $f\perp\mathbf 1$; reason: Lean representation, equivalent statements.
--   - encoding: the square root $i$ of $-1$ → a parameter, every choice; reason: the construction depends on it and the claim holds for each.
-- source:
--   Chao, Li, Gao, Wang, Once-Paid Subsequences and the Cost of Min-Plus Approximation, STOC 2027 submission (manuscript sha256 9dc21472…), p. 37, App. A.3, LPS family (PDF p. 39), citing [LPS88] and [MdlH06, Section 2]

import Mathlib
import Definitions.Def_OncePaid_Sparse_BipHost
import Definitions.Def_OncePaid_Sparse_LPS

namespace OncePaid.Sparse

/-- App. A.3, the LPS family, p. 37. For every prime `ℓ ≡ 305 (mod 404)` and every `i ∈ 𝔽_ℓ` with
`i² = −1`: `ℓ ≡ 1 (mod 4)` and `ℓ ≡ 2 (mod 101)`; `101` is not a square mod `ℓ` and `2` is not a
square mod `101`; and the LPS graph `X_{101,ℓ}` (the Cayley graph of `PGL(2, 𝔽_ℓ)` for the `102`
quaternion generators) is a simple connected bipartite `102`-regular graph on `ℓ(ℓ² − 1)`
vertices: every edge joins the square-determinant class to its complement, each class has
`ℓ(ℓ² − 1)/2` elements, every vertex has `102` neighbours, the host `H_ℓ` between the two classes
is `102`-biregular, and all its nontrivial biadjacency singular values are at most `2√101`, with
`2√101 < 21`. -/
theorem lps_family (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ % 404 = 305) (i : ZMod ℓ) (hi : i ^ 2 = -1) :
    ℓ % 4 = 1 ∧ ℓ % 101 = 2 ∧ ¬ IsSquare (101 : ZMod ℓ) ∧ ¬ IsSquare (2 : ZMod 101) ∧
    Nat.card (Matrix.ProjGenLinGroup (Fin 2) (ZMod ℓ)) = ℓ * (ℓ ^ 2 - 1) ∧
    (lpsGraph ℓ i).Connected ∧
    (∀ g h : Matrix.ProjGenLinGroup (Fin 2) (ZMod ℓ), (lpsGraph ℓ i).Adj g h →
      (IsSquareClass ℓ g ↔ ¬ IsSquareClass ℓ h)) ∧
    Fintype.card (lpsLeft ℓ) = lpsN ℓ ∧ Fintype.card (lpsRight ℓ) = lpsN ℓ ∧
    (∀ g : Matrix.ProjGenLinGroup (Fin 2) (ZMod ℓ), ((lpsGraph ℓ i).neighborSet g).ncard = 102) ∧
    IsBiregular (lpsAdj ℓ i) 102 ∧
    NontrivialSingularValuesLe (lpsAdj ℓ i) (2 * Real.sqrt 101) ∧
    2 * Real.sqrt 101 < 21 := by sorry

end OncePaid.Sparse
