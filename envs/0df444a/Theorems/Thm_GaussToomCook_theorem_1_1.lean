-- Prove2me | Theorems.Thm_GaussToomCook_theorem_1_1
-- name    : GaussToomCook.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:47:09.592221+00:00
-- url     : https://prove2.me/theorems/77717ad9-0fc6-43ad-80cb-68cc9be34ddf
-- title:
--   Theorem 1.1 — every Gaussian Toom–Cook-$k$ ($k\ge2$) has at least $2k-4$ divisions by non-units and $2k-7$ divisions not by a unit times a power of $1+i$
-- statement:
--   Let $k\ge2$ and let $S$ be a set of $2k-1$ pairwise non-proportional nonzero points of $\mathbb Z[i]^2$ (evaluation points of Gaussian Toom–Cook-$k$). Consider any interpolation phase (V) on $S$: a sequence of vectors, starting from the rows of the Vandermonde matrix $V(S)$, in which each new vector is $\lambda v+\mu u$ ($\lambda,\mu\in\mathbb Z[i]$) or $v/\lambda$ ($\lambda\in\mathbb Z[i]\setminus\{0\}$) for earlier vectors $v,u$, and which reaches every standard basis vector $q_0,\dots,q_{2k-2}$. Then
--
--   1. the number of divisions $v/\lambda$ with $\lambda$ not a unit is at least $2k-4$;
--   2. the number of divisions $v/\lambda$ with $\lambda$ not of the form $u\,(1+i)^m$ ($u\in\mathbb Z[i]^\times$, $m\ge0$) is at least $2k-7$.
--
--   Divisions by a unit times a power of $1+i$ are cheap in binary arithmetic (a division by $1+i$ is a multiplication by $1-i$ and a halving), so the second count is the number of non-trivial divisions. Proposition 9.7 of the paper shows that $\max\{0,2k-7\}$ is attained.
--
--   **Formalization Note** The divisions counted are those of the interpolation phase, which §9.1 models as the sequence above; divisions elsewhere in the algorithm only add to the count. $1+i$ is written `⟨1, 1⟩ : GaussianInt`. The bounds are compared in $\mathbb Z$.
--
--   Differences from the source:
--   - reading: Every Gaussian Toom–Cook-k algorithm … contains at least … divisions → for every evaluation set S and every successful §9.1 interpolation sequence on S, its division counts; reason: the paper proves Theorem 1.1 by counting the divisions of phase (V) in the §9.1 model ("we will show that the interpolation phase (V) requires many divisions", p. 29); divisions in other phases only add to the count.
--   - encoding: S ⊂ ℤ[i]² ∖ {(0,0)}, 2k−1 pairs, no two scalar multiples over ℚ(i)^× (§6, p. 13) → S : Fin (2k−1) → ℤ[i] × ℤ[i] with S j ≠ (0,0) and (S j).1·(S j').2 − (S j').1·(S j).2 ≠ 0 for j ≠ j' (IsEvalPoints); reason: for nonzero pairs, non-proportionality over ℚ(i)^× is equivalent to the nonvanishing cross product, which also makes the indexing injective.
--   - encoding: W = ⊕_{j=0}^{2k−1} ℚ(i) q_j with ℤ[i] scalars (p. 30) → vectors Fin (2k−1) → ℂ, ℤ[i] acting through GaussianInt.toComplex, q_j = Pi.single j 1; reason: every vector the sequence can produce lies in ℚ(i)^{2k−1} ⊂ ℂ^{2k−1}, so no instance changes; the upper index 2k−1 of the direct sum is a typo for 2k−2 (the basis is q_0, …, q_{2k−2} and the dimension is |S| = 2k−1).
--   - encoding: sets W_i = W_{i−1} ∪ {w_i}, operands v, u ∈ W_{i−1} (p. 30) → lists, each step appending w_i and naming its operands by position; W₀ lists the rows of V(S) in the order of S; reason: the same sequences of vectors; a position names an element of W_{i−1}.
--   - generalization: the procedure ends when every q_j has been added → any valid program whose final list contains every q_j, possibly with further steps; reason: steps after the last q_j can only add divisions, so the bound for these programs specializes to the paper's sequences (each is such a program).
--   - encoding: the number of divisions → numDiv: the number of steps of type (ii) whose divisor satisfies the predicate, with multiplicity; reason: a division is a step of the sequence.
--   - encoding: a division by a non-unit; by a Gaussian integer which is not a power of 1 + i times a unit → ¬ IsUnit λ; ¬ ∃ m : ℕ, ∃ u : ℤ[i]ˣ, λ = u · (1 + i)^m; reason: m = 0 is a power of 1 + i, so units are among the excluded divisors.
--   - encoding: bounds such as 2k − 2 − Nr(p) → compared in ℤ; reason: the bound may be negative for small k; natural-number subtraction would truncate it.
-- source:
--   Y. Spiizer, R. S. Steiner, Rational and Gaussian long integer multiplication, manuscript (STOC 2027 submission; held version sha256 f50b53628a53a03bd55785424af241d0ac5ea751714330838e4017b90b27ad70), §1.1, Theorem 1.1, p. 4 (PDF p. 6); proved via Theorem 9.3, p. 31 (PDF p. 33)

import Mathlib
import Definitions.Def_GaussToomCook_IsEvalPoints
import Definitions.Def_GaussToomCook_IsInterpolation

namespace GaussToomCook

/-- **Theorem 1.1**, Spiizer, Steiner, *Rational and Gaussian long integer multiplication*, manuscript
(STOC 2027 submission; sha256 f50b5362…27ad70), §1.1, p. 4 (PDF 6).

"Every Gaussian Toom–Cook-k algorithm with k ≥ 2 contains at least 2k − 4 divisions (by a non-unit) and
2k − 7 divisions by a Gaussian integer which is not a power of 1 + i times a unit."

For every `k ≥ 2`, every set `S` of `2k − 1` pairwise non-proportional nonzero points of `ℤ[i]²`, and every
interpolation phase (V) on `S` (a sequence of ℤ[i]-linear combinations and divisions by nonzero Gaussian
integers, starting from the rows of `V(S)` and reaching every standard basis vector), the number of
divisions by non-units is at least `2k − 4`, and the number of divisions by Gaussian integers not of the
form `u · (1 + i)^m` (`u` a unit, `m ≥ 0`) is at least `2k − 7`.

**Formalization Note.** The divisions counted are those of the interpolation phase, the paper's model
(§9.1); divisions elsewhere in the algorithm only add to the count. `⟨1, 1⟩ : GaussianInt` is `1 + i`.
`m = 0` is allowed, so units are among the excluded divisors. Bounds are compared in `ℤ`. -/
theorem theorem_1_1 (k : ℕ) (hk : 2 ≤ k) (S : Fin (2 * k - 1) → GaussianInt × GaussianInt)
    (hS : IsEvalPoints k S) (prog : List Step) (hprog : IsInterpolation k S prog) :
    2 * (k : ℤ) - 4 ≤ (numDiv (fun l => ¬ IsUnit l) prog : ℤ) ∧
    2 * (k : ℤ) - 7 ≤ (numDiv (fun l => ¬ ∃ (m : ℕ) (u : GaussianIntˣ),
      l = (u : GaussianInt) * (⟨1, 1⟩ : GaussianInt) ^ m) prog : ℤ) := by sorry

end GaussToomCook
