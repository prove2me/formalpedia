-- Prove2me | Theorems.Thm_GaussToomCook_proposition_9_4
-- name    : GaussToomCook.proposition_9_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:46:59.333999+00:00
-- url     : https://prove2.me/theorems/5b7a6c62-a3d8-48b9-b137-6142966c9f05
-- title:
--   Proposition 9.4 — divisions by multiples of $p$ at least the elementary divisors of $V(S)$ divisible by $p$
-- statement:
--   Let $k\ge1$, let $S$ be evaluation points for Gaussian Toom–Cook-$k$, and let $p\in\mathbb Z[i]$ be a Gaussian prime. Let $e_1\mid\cdots\mid e_{2k-1}$ be the elementary divisors of the Vandermonde matrix $V(S)$. Then every interpolation phase (V) on $S$, i.e. every sequence of $\mathbb Z[i]$-linear combinations $\lambda v+\mu u$ and divisions $v/\lambda$ ($\lambda\in\mathbb Z[i]\setminus\{0\}$) that starts from the rows of $V(S)$ and reaches every standard basis vector $q_0,\dots,q_{2k-2}$, satisfies
--   $$\#\{\text{divisions by multiples of }p\}\ \ge\ \#\{\,j:\ p\mid e_j\,\}.$$
--
--   Combined with Proposition 9.5 it gives Theorem 9.3.
--
--   Differences from the source:
--   - reading: the interpolation phase (V) of the Gaussian Toom–Cook-k algorithm → a successful §9.1 sequence (IsInterpolation k S prog) for evaluation points S; reason: §9.1 (p. 30) models phase (V) as this sequence of ℤ[i]-linear combinations and divisions; the statement holds for every such sequence.
--   - encoding: S ⊂ ℤ[i]² ∖ {(0,0)}, 2k−1 pairs, no two scalar multiples over ℚ(i)^× (§6, p. 13) → S : Fin (2k−1) → ℤ[i] × ℤ[i] with S j ≠ (0,0) and (S j).1·(S j').2 − (S j').1·(S j).2 ≠ 0 for j ≠ j' (IsEvalPoints); reason: for nonzero pairs, non-proportionality over ℚ(i)^× is equivalent to the nonvanishing cross product, which also makes the indexing injective.
--   - encoding: W = ⊕_{j=0}^{2k−1} ℚ(i) q_j with ℤ[i] scalars (p. 30) → vectors Fin (2k−1) → ℂ, ℤ[i] acting through GaussianInt.toComplex, q_j = Pi.single j 1; reason: every vector the sequence can produce lies in ℚ(i)^{2k−1} ⊂ ℂ^{2k−1}, so no instance changes; the upper index 2k−1 of the direct sum is a typo for 2k−2 (the basis is q_0, …, q_{2k−2} and the dimension is |S| = 2k−1).
--   - encoding: sets W_i = W_{i−1} ∪ {w_i}, operands v, u ∈ W_{i−1} (p. 30) → lists, each step appending w_i and naming its operands by position; W₀ lists the rows of V(S) in the order of S; reason: the same sequences of vectors; a position names an element of W_{i−1}.
--   - generalization: the procedure ends when every q_j has been added → any valid program whose final list contains every q_j, possibly with further steps; reason: steps after the last q_j can only add divisions, so the bound for these programs specializes to the paper's sequences (each is such a program).
--   - encoding: the number of divisions → numDiv: the number of steps of type (ii) whose divisor satisfies the predicate, with multiplicity; reason: a division is a step of the sequence.
--   - encoding: the elementary divisors e₁ | e₂ | ⋯ of a matrix → the diagonal d of any Smith normal form U A V = diag(d) with U, V of unit determinant and d i ∣ d j for i ≤ j (IsSmithNF); reason: over a PID the form exists and d is unique up to units, so a statement for every such d is a statement about the elementary divisors.
-- source:
--   Y. Spiizer, R. S. Steiner, Rational and Gaussian long integer multiplication, manuscript (STOC 2027 submission; held version sha256 f50b53628a53a03bd55785424af241d0ac5ea751714330838e4017b90b27ad70), §9.3, Proposition 9.4, p. 31 (PDF p. 33); proof pp. 32–33 (PDF pp. 34–35)

import Mathlib
import Definitions.Def_GaussToomCook_IsEvalPoints
import Definitions.Def_GaussToomCook_vandMatrix
import Definitions.Def_GaussToomCook_IsInterpolation
import Definitions.Def_GaussToomCook_IsSmithNF

namespace GaussToomCook

/-- **Proposition 9.4**, Spiizer, Steiner, *Rational and Gaussian long integer multiplication*,
manuscript (STOC 2027 submission; sha256 f50b5362…27ad70), §9.3, p. 31 (PDF 33); proof pp. 32–33.

Let `p ∈ ℤ[i]` be a Gaussian prime. In every interpolation phase (V) of Gaussian Toom–Cook-k (a sequence
of ℤ[i]-linear combinations and divisions by nonzero Gaussian integers that starts from the rows of
`V(S)` and reaches every standard basis vector `q_j`), the number of divisions by multiples of `p` is at
least the number of elementary divisors of `V(S)` divisible by `p`.

**Formalization Note.** Elementary divisors: the diagonal of any Smith normal form with divisibility
chain (`IsSmithNF`). Divisions are counted as steps, with multiplicity (`numDiv`). -/
theorem proposition_9_4 (k : ℕ) (hk : 0 < k) (S : Fin (2 * k - 1) → GaussianInt × GaussianInt)
    (hS : IsEvalPoints k S) (prog : List Step) (hprog : IsInterpolation k S prog)
    (p : GaussianInt) (hp : Prime p)
    (U V : Matrix (Fin (2 * k - 1)) (Fin (2 * k - 1)) GaussianInt) (d : Fin (2 * k - 1) → GaussianInt)
    (hd : IsSmithNF (vandMatrix k S) U V d) :
    pdvdCount p d ≤ numDiv (fun l => p ∣ l) prog := by sorry

end GaussToomCook
