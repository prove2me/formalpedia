-- Prove2me | Theorems.Thm_ModLatSVP_packing_bound
-- name    : ModLatSVP.packing_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:12:07.511081+00:00
-- url     : https://prove2.me/theorems/02c25519-61e3-416e-9bc4-d3d71665df13
-- title:
--   Packing bound — a ball of radius $R$ holds at most $(1+4R/\lambda_1)^m$ lattice points
-- statement:
--   Let $L$ be an $m$-dimensional Euclidean lattice with minimum $H=\lambda_1(L)$. For every point $c$ of the span of $L$ and every $R\ge0$, the closed ball $B(c,R)$ contains finitely many points of $L$, and
--
--   $$\#\big(L\cap B(c,R)\big)\le\Big(1+\frac{4R}{H}\Big)^{m}.$$
--
--   The paper applies it to the blocks $L_k$ (of dimension $d$) to count the branches of the backward search in Lemma 3.2, and to count the projected points in the CVP recursion of Theorem 3.5.
--
--   Differences from the source:
--   - generalization: a block L_k of dimension d, a ball of radius R ≥ 0 with a center of rational coordinates → any m-dimensional lattice with positive definite real Gram matrix, any real center of the span; reason: specializes to the blocks with m = d and rational centers
--   - encoding: the number of points of L_k in a ball → Set.Finite and Set.ncard of the integer coefficient vectors x with (x − c)ᵀG(x − c) ≤ R²; reason: the Gram-matrix model; finiteness is stated so that ncard is the true count
-- source:
--   Kim, Lee, Son, Exact SVP and CVP in Structured Lattices: Polynomial-Space Algorithms and Reductions, STOC 2027 submission (manuscript sha256 e7151fad…), proof of Lemma 3.2, p.18 (PDF p.18)

import Mathlib
import Definitions.Def_ModLatSVP_lam1

namespace ModLatSVP

/-- **Packing bound, proof of Lemma 3.2, p.18.** Kim, Lee, Son, *Exact SVP and CVP in Structured
Lattices: Polynomial-Space Algorithms and Reductions*, STOC 2027 submission (manuscript sha256
e7151fad…): "By a standard packing bound, a ball of radius R contains at most (1 + 4R/H_k)^d points of
L_k."

For every `m`-dimensional lattice `L` with positive definite Gram matrix `G` and minimum `H = λ₁(L)`, every
center `c` of the span and every radius `R ≥ 0`, the closed ball `B(c, R)` contains finitely many points
of `L`, and at most `(1 + 4R/H)^m` of them.

**Formalization Note.** Stated for any dimension `m` (the paper applies it to blocks of dimension `d`)
and any real center of the span (the paper's centers have rational coordinates). `R ≥ 0` is Lemma 3.2's
"R ≥ 0". For `m = 0` both sides are `1`. -/
theorem packing_bound (m : ℕ) (G : Matrix (Fin m) (Fin m) ℝ) (hG : G.PosDef) (c : Fin m → ℝ)
    (R : ℝ) (hR : 0 ≤ R) :
    {x : Fin m → ℤ | qf G (intVec x - c) ≤ R ^ 2}.Finite ∧
      (({x : Fin m → ℤ | qf G (intVec x - c) ≤ R ^ 2}.ncard : ℕ) : ℝ) ≤
        (1 + 4 * R / lam1 G) ^ m := by sorry

end ModLatSVP
