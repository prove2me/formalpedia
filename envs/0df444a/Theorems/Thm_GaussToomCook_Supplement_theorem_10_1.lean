-- Prove2me | Theorems.Thm_GaussToomCook_Supplement_theorem_10_1
-- name    : GaussToomCook.Supplement.theorem_10_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T23:56:42.818471+00:00
-- url     : https://prove2.me/theorems/f743129c-4623-48bd-b9e3-99d33b98979c
-- title:
--   Theorem 10.1 — the division factor is divisible by $\prod_{p\nmid 2}p^{\lfloor(2k-2)/(\mathrm{Nr}(p)+1)\rfloor}$
-- statement:
--   Let $k\ge1$ and let $S$ be $2k-1$ evaluation points of Gaussian Toom–Cook-$k$ (nonzero pairs in $\mathbb Z[i]^2$, pairwise non-proportional over $\mathbb Q(i)$). The interpolation linear transformation of the algorithm is $W^T=V(S)^{-1}$, the inverse of the evaluation map $P\mapsto(P(x,y))_{(x,y)\in S}$ on homogeneous polynomials of degree $2k-2$ in the monomial basis. Let $\alpha$ be the division factor of $W^T$: a nonzero Gaussian integer of minimal norm such that $2^j\alpha W^T$ has Gaussian-integer entries for some $j\ge0$. Let $\mathcal P$ be a representative set of the Gaussian primes up to association. Then
--   $$\prod_{\substack{p\in\mathcal P\\ p\nmid 2}}p^{\left\lfloor\frac{2k-2}{\mathrm{Nr}(p)+1}\right\rfloor}\ \Big|\ \alpha .$$
--   Only primes with $\mathrm{Nr}(p)+1\le 2k-2$ have a positive exponent, so the product is finite. The Lean statement asserts: for every finite set $P$ of pairwise non-associated Gaussian primes none of which divides $2$, $\prod_{p\in P}p^{\lfloor(2k-2)/(\mathrm{Nr}(p)+1)\rfloor}$ divides $\alpha$.
--
--   The theorem is the Gaussian analogue of the Nissim–Schwartz–Spiizer lower bound on the division factor of rational Toom–Cook algorithms; it shows that the denominators of every Gaussian Toom–Cook-$k$ interpolation grow with $k$ at every odd Gaussian prime of small norm.
--
--   **Formalization Note** $V(S)^{-1}$ is computed over $\mathbb C$ from the published `vandMatrix` (it is invertible because the points are pairwise non-proportional). $\mathrm{Nr}$ is the published norm, and the floor is natural-number division.
--
--   Differences from the source:
--   - reading: the division factor of the algorithm (§10, after [NSS25, Def. 2.4]: the least $\alpha$ for which an equivalent algorithm with only divisions by powers of $2$ computes $\alpha$ times the product) → the division factor (§2.2.3) of the interpolation matrix $W^T=V(S)^{-1}$; reason: §2.2.3 defines the division factor of a matrix, and the proof of Theorem 10.1 (p. 34) works with exactly the denominators of $W^T$
--   - reading: "the Gaussian integer with minimal norm" → the nonzero Gaussian integer with minimal norm; reason: $\alpha=0$ trivially clears every matrix, so minimality is meant among nonzero elements
--   - encoding: the product over a representative set $\mathcal P$ with $p\nmid2$ → for every finite set of pairwise non-associated primes not dividing $2$, the product over it divides $\alpha$; reason: only finitely many factors differ from $1$, so taking the set of contributing representatives gives (102), and every such product divides (102)
--   - encoding: $W^T$ over $\mathbb Q(i)$ → $V(S)^{-1}$ over $\mathbb C$; reason: the inverse of a matrix over $\mathbb Z[i]$ has entries in $\mathbb Q(i)$, and integrality of entries is tested through the embedding $\mathbb Z[i]\to\mathbb C$
-- source:
--   Y. Spiizer, R. S. Steiner, Rational and Gaussian long integer multiplication, manuscript (STOC 2027 submission; held version sha256 f50b53628a53a03bd55785424af241d0ac5ea751714330838e4017b90b27ad70), §10, Theorem 10.1, eq. (102), p. 34 (PDF p. 36); division factor §2.2.3, p. 8 (PDF p. 10)

import Mathlib
import Definitions.Def_GaussToomCook_Nr
import Definitions.Def_GaussToomCook_IsEvalPoints
import Definitions.Def_GaussToomCook_vandMatrix
import Definitions.Def_GaussToomCook_Supplement_IsDivisionFactor

namespace GaussToomCook.Supplement

/-- **Theorem 10.1** (lower bound on the division factor), Spiizer, Steiner, *Rational and Gaussian long integer
multiplication*, manuscript (STOC 2027 submission; sha256 f50b5362…27ad70), §10, p. 34 (PDF 36), eq. (102):
"Denote by `𝒫 ⊆ ℤ[i]` a representative set of all Gaussian primes up to association (multiplication by unit).
The division factor of any Gaussian Toom–Cook-k algorithm is divisible by
`∏_{p ∈ 𝒫, p ∤ 2} p^{⌊(2k−2)/(Nr(p)+1)⌋}`."

Let `k ≥ 1`, `S` be `2k − 1` evaluation points, and `α` a division factor (§2.2.3) of the interpolation matrix
`W^T = V(S)^{−1}`. Then for every finite set `P` of pairwise non-associated Gaussian primes none of which divides
`2`, `∏_{p ∈ P} p^{⌊(2k−2)/(Nr(p)+1)⌋}` divides `α`.

**Formalization Note.** `V(S)^{−1}` is computed over `ℂ` (`V(S)` is invertible because the points are pairwise
non-proportional). Only primes with `Nr(p) + 1 ≤ 2k − 2` have a positive exponent, so (102) is a finite product;
taking `P` to contain every such prime (one per association class) gives (102) for any representative set `𝒫`.
The floor is natural-number division. -/
theorem theorem_10_1 (k : ℕ) (hk : 0 < k) (S : Fin (2 * k - 1) → GaussianInt × GaussianInt)
    (hS : GaussToomCook.IsEvalPoints k S) (α : GaussianInt)
    (hα : IsDivisionFactor α ((GaussToomCook.vandMatrix k S).map GaussianInt.toComplex)⁻¹)
    (P : Finset GaussianInt) (hPprime : ∀ p ∈ P, Prime p) (hP2 : ∀ p ∈ P, ¬ p ∣ 2)
    (hPassoc : (P : Set GaussianInt).Pairwise fun p q => ¬ Associated p q) :
    ∏ p ∈ P, p ^ ((2 * k - 2) / (GaussToomCook.Nr p + 1)) ∣ α := by sorry

end GaussToomCook.Supplement
