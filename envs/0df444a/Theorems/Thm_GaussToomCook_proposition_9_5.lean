-- Prove2me | Theorems.Thm_GaussToomCook_proposition_9_5
-- name    : GaussToomCook.proposition_9_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:46:27.985356+00:00
-- url     : https://prove2.me/theorems/91fec412-031a-411f-a685-d9125e55b640
-- title:
--   Proposition 9.5 — at least $2k-2-\mathrm{Nr}(p)$ elementary divisors of $V(S)$ are divisible by $p$
-- statement:
--   Let $k\ge1$, let $S$ be evaluation points for Gaussian Toom–Cook-$k$ ($2k-1$ pairwise non-proportional nonzero points of $\mathbb Z[i]^2$), and let $p\in\mathbb Z[i]$ be a Gaussian prime. Let $e_1\mid e_2\mid\cdots\mid e_{2k-1}$ be the elementary divisors of the Vandermonde matrix $V(S)$ of eq. (85). Then
--   $$\#\{\,j:\ p\mid e_j\,\}\ \ge\ 2k-2-\mathrm{Nr}(p).$$
--
--   Together with Proposition 9.4 it gives Theorem 9.3. For $p=1+i$ the bound is $2k-4$, for $p=2\pm i$ it is $2k-7$.
--
--   Differences from the source:
--   - encoding: S ⊂ ℤ[i]² ∖ {(0,0)}, 2k−1 pairs, no two scalar multiples over ℚ(i)^× (§6, p. 13) → S : Fin (2k−1) → ℤ[i] × ℤ[i] with S j ≠ (0,0) and (S j).1·(S j').2 − (S j').1·(S j).2 ≠ 0 for j ≠ j' (IsEvalPoints); reason: for nonzero pairs, non-proportionality over ℚ(i)^× is equivalent to the nonvanishing cross product, which also makes the indexing injective.
--   - encoding: the elementary divisors e₁ | e₂ | ⋯ of a matrix → the diagonal d of any Smith normal form U A V = diag(d) with U, V of unit determinant and d i ∣ d j for i ≤ j (IsSmithNF); reason: over a PID the form exists and d is unique up to units, so a statement for every such d is a statement about the elementary divisors.
--   - encoding: Nr(p) = |ℤ[i]/pℤ[i]| → Nr p = |Zsqrtd.norm p| (a² + b² for p = a + bi); reason: equal for p ≠ 0, and Gaussian primes are nonzero.
--   - encoding: bounds such as 2k − 2 − Nr(p) → compared in ℤ; reason: the bound may be negative for small k; natural-number subtraction would truncate it.
-- source:
--   Y. Spiizer, R. S. Steiner, Rational and Gaussian long integer multiplication, manuscript (STOC 2027 submission; held version sha256 f50b53628a53a03bd55785424af241d0ac5ea751714330838e4017b90b27ad70), §9.3, Proposition 9.5, p. 31 (PDF p. 33); proof pp. 31–32 (PDF pp. 33–34)

import Mathlib
import Definitions.Def_GaussToomCook_Nr
import Definitions.Def_GaussToomCook_IsEvalPoints
import Definitions.Def_GaussToomCook_vandMatrix
import Definitions.Def_GaussToomCook_IsSmithNF

namespace GaussToomCook

/-- **Proposition 9.5**, Spiizer, Steiner, *Rational and Gaussian long integer multiplication*,
manuscript (STOC 2027 submission; sha256 f50b5362…27ad70), §9.3, p. 31 (PDF 33); proof pp. 31–32.

Let `p ∈ ℤ[i]` be a Gaussian prime and `V(S)` the Vandermonde matrix (85) of the evaluation points of
Gaussian Toom–Cook-k. Then the number of elementary divisors of `V(S)` divisible by `p` is at least
`2k − 2 − Nr(p)`.

**Formalization Note.** The elementary divisors are the diagonal `d` of any Smith normal form
`U V(S) V = diag(d)` with `d 0 ∣ d 1 ∣ ⋯` over `ℤ[i]`; the bound is compared in `ℤ`, where it is
nonpositive for small `k`. -/
theorem proposition_9_5 (k : ℕ) (hk : 0 < k) (S : Fin (2 * k - 1) → GaussianInt × GaussianInt)
    (hS : IsEvalPoints k S) (p : GaussianInt) (hp : Prime p)
    (U V : Matrix (Fin (2 * k - 1)) (Fin (2 * k - 1)) GaussianInt) (d : Fin (2 * k - 1) → GaussianInt)
    (hd : IsSmithNF (vandMatrix k S) U V d) :
    2 * (k : ℤ) - 2 - (Nr p : ℤ) ≤ (pdvdCount p d : ℤ) := by sorry

end GaussToomCook
