-- Prove2me | Theorems.Thm_GaussToomCook_theorem_9_3
-- name    : GaussToomCook.theorem_9_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:47:17.941438+00:00
-- url     : https://prove2.me/theorems/a892e41e-9f78-4fa5-862f-bf48892f5291
-- title:
--   Theorem 9.3 — at least $2k-2-\mathrm{Nr}(p)$ divisions by multiples of $p$
-- statement:
--   Let $k\ge1$, let $S$ be evaluation points for Gaussian Toom–Cook-$k$, and let $p\in\mathbb Z[i]$ be a Gaussian prime. Every interpolation phase (V) on $S$, i.e. every sequence of $\mathbb Z[i]$-linear combinations and divisions by nonzero Gaussian integers that starts from the rows of $V(S)$ and reaches every standard basis vector, contains
--   $$\#\{\text{divisions by multiples of }p\}\ \ge\ 2k-2-\mathrm{Nr}(p).$$
--
--   Theorem 1.1 follows by taking $p=1+i$ ($\mathrm{Nr}=2$) and $p=2+i$ ($\mathrm{Nr}=5$).
--
--   Differences from the source:
--   - reading: the interpolation phase (V) of the Gaussian Toom–Cook-k algorithm → a successful §9.1 sequence (IsInterpolation k S prog) for evaluation points S; reason: §9.1 (p. 30) models phase (V) as this sequence of ℤ[i]-linear combinations and divisions; the statement holds for every such sequence.
--   - encoding: S ⊂ ℤ[i]² ∖ {(0,0)}, 2k−1 pairs, no two scalar multiples over ℚ(i)^× (§6, p. 13) → S : Fin (2k−1) → ℤ[i] × ℤ[i] with S j ≠ (0,0) and (S j).1·(S j').2 − (S j').1·(S j).2 ≠ 0 for j ≠ j' (IsEvalPoints); reason: for nonzero pairs, non-proportionality over ℚ(i)^× is equivalent to the nonvanishing cross product, which also makes the indexing injective.
--   - encoding: W = ⊕_{j=0}^{2k−1} ℚ(i) q_j with ℤ[i] scalars (p. 30) → vectors Fin (2k−1) → ℂ, ℤ[i] acting through GaussianInt.toComplex, q_j = Pi.single j 1; reason: every vector the sequence can produce lies in ℚ(i)^{2k−1} ⊂ ℂ^{2k−1}, so no instance changes; the upper index 2k−1 of the direct sum is a typo for 2k−2 (the basis is q_0, …, q_{2k−2} and the dimension is |S| = 2k−1).
--   - encoding: sets W_i = W_{i−1} ∪ {w_i}, operands v, u ∈ W_{i−1} (p. 30) → lists, each step appending w_i and naming its operands by position; W₀ lists the rows of V(S) in the order of S; reason: the same sequences of vectors; a position names an element of W_{i−1}.
--   - generalization: the procedure ends when every q_j has been added → any valid program whose final list contains every q_j, possibly with further steps; reason: steps after the last q_j can only add divisions, so the bound for these programs specializes to the paper's sequences (each is such a program).
--   - encoding: the number of divisions → numDiv: the number of steps of type (ii) whose divisor satisfies the predicate, with multiplicity; reason: a division is a step of the sequence.
--   - encoding: Nr(p) = |ℤ[i]/pℤ[i]| → Nr p = |Zsqrtd.norm p| (a² + b² for p = a + bi); reason: equal for p ≠ 0, and Gaussian primes are nonzero.
--   - encoding: bounds such as 2k − 2 − Nr(p) → compared in ℤ; reason: the bound may be negative for small k; natural-number subtraction would truncate it.
-- source:
--   Y. Spiizer, R. S. Steiner, Rational and Gaussian long integer multiplication, manuscript (STOC 2027 submission; held version sha256 f50b53628a53a03bd55785424af241d0ac5ea751714330838e4017b90b27ad70), §9.3, Theorem 9.3, p. 31 (PDF p. 33)

import Mathlib
import Definitions.Def_GaussToomCook_Nr
import Definitions.Def_GaussToomCook_IsEvalPoints
import Definitions.Def_GaussToomCook_IsInterpolation

namespace GaussToomCook

/-- **Theorem 9.3**, Spiizer, Steiner, *Rational and Gaussian long integer multiplication*, manuscript
(STOC 2027 submission; sha256 f50b5362…27ad70), §9.3, p. 31 (PDF 33).

Let `p ∈ ℤ[i]` be a Gaussian prime. The number of divisions by multiples of `p` in the interpolation
phase (V) of the Gaussian Toom–Cook-k algorithm is at least `2k − 2 − Nr(p)`, for every set `S` of
evaluation points and every successful interpolation program.

**Formalization Note.** The bound is compared in `ℤ`. Divisions are steps of type (ii), counted with
multiplicity. -/
theorem theorem_9_3 (k : ℕ) (hk : 0 < k) (S : Fin (2 * k - 1) → GaussianInt × GaussianInt)
    (hS : IsEvalPoints k S) (prog : List Step) (hprog : IsInterpolation k S prog)
    (p : GaussianInt) (hp : Prime p) :
    2 * (k : ℤ) - 2 - (Nr p : ℤ) ≤ (numDiv (fun l => p ∣ l) prog : ℤ) := by sorry

end GaussToomCook
