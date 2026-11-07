-- Prove2me | Theorems.Thm_GaussToomCook_proposition_9_1_det
-- name    : GaussToomCook.proposition_9_1_det
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:45:56.098841+00:00
-- url     : https://prove2.me/theorems/32b6eb0c-2b16-4f4a-984e-3f10d73b215b
-- title:
--   Proposition 9.1, proof — $p\mid\det V(T)$ when $|T|\ge \mathrm{Nr}(p)+2$
-- statement:
--   Let $p\in\mathbb Z[i]$ be a Gaussian prime and let $T=((x_t,y_t))_{0\le t\le n-1}$ be any $n$ points of $\mathbb Z[i]^2$ with
--   $$n\ge \mathrm{Nr}(p)+2 .$$
--   Then $p$ divides the determinant of the projective Vandermonde matrix
--   $$V(T)=\big[x_t^{\,j}\,y_t^{\,n-1-j}\big]_{0\le t,j\le n-1},\qquad \det V(T)=\pm\prod_{s<t}(x_s y_t-x_t y_s).$$
--
--   This is the determinant step of the proof of Proposition 9.1: modulo $p$ the points project to the projective line over the field $\mathbb Z[i]/p\mathbb Z[i]$, which has only $\mathrm{Nr}(p)+1$ points. The proof of Proposition 9.5 applies it to the subsets $T\subseteq S$.
--
--   Differences from the source:
--   - generalization: |S| = 2k − 1 ≥ Nr(p) + 2 pairwise non-proportional nonzero evaluation points → any family of n ≥ Nr(p) + 2 points of ℤ[i]²; reason: the proof of Proposition 9.5 applies the step to subsets T ⊆ S of any size n; with repeated, proportional or zero points the determinant only gains factors (or vanishes), and the evaluation points are a special case.
--   - encoding: V(S) (85) → Matrix.projVandermonde of the two coordinates, entries x^j y^{n−1−j}; reason: Mathlib's definition is (85) with x, y the two coordinates.
--   - encoding: Nr(p) = |ℤ[i]/pℤ[i]| → Nr p = |Zsqrtd.norm p| (a² + b² for p = a + bi); reason: equal for p ≠ 0, and Gaussian primes are nonzero.
-- source:
--   Y. Spiizer, R. S. Steiner, Rational and Gaussian long integer multiplication, manuscript (STOC 2027 submission; held version sha256 f50b53628a53a03bd55785424af241d0ac5ea751714330838e4017b90b27ad70), §9.2, proof of Proposition 9.1, pp. 30–31 (PDF pp. 32–33); eq. (89)

import Mathlib
import Definitions.Def_GaussToomCook_Nr

namespace GaussToomCook

/-- **Proposition 9.1, proof: the Vandermonde determinant is divisible by `p`**, Spiizer, Steiner,
*Rational and Gaussian long integer multiplication*, manuscript (STOC 2027 submission; sha256
f50b5362…27ad70), §9.2, pp. 30–31 (PDF 32–33).

Let `p` be a Gaussian prime and `T` a family of `n ≥ Nr(p) + 2` points of `ℤ[i]²`. Then `p` divides the
determinant of the projective Vandermonde matrix `V(T) = [x^j y^{n−1−j}]_{(x,y)∈T, 0≤j≤n−1}`. (The
projective line over `ℤ[i]/pℤ[i]` has only `Nr(p) + 1` points; points `≡ (0,0) mod p` make the
determinant divisible by `p` directly.)

**Formalization Note.** Stated for any finite family of points, not only for a set of pairwise
non-proportional nonzero points: with repeated or proportional points the determinant (89) is `0`.
`V(T)` is Mathlib's `Matrix.projVandermonde` of the two coordinates. No point is assumed nonzero
modulo `p`. -/
theorem proposition_9_1_det {n : ℕ} (T : Fin n → GaussianInt × GaussianInt) (p : GaussianInt)
    (hp : Prime p) (hn : Nr p + 2 ≤ n) :
    p ∣ (Matrix.projVandermonde (fun t => (T t).1) (fun t => (T t).2)).det := by sorry

end GaussToomCook
