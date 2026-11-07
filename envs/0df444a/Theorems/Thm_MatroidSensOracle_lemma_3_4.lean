-- Prove2me | Theorems.Thm_MatroidSensOracle_lemma_3_4
-- name    : MatroidSensOracle.lemma_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:50:47.9822+00:00
-- url     : https://prove2.me/theorems/09ba28f7-530b-4699-8f60-e6edaf3eb377
-- title:
--   Lemma 3.4 (Encoding Common Bases): $\det(ADB^T)=Y^{NW}\sum_S\alpha_S\prod x_e\,Y^{\mathrm{wt}(S)}$, and its min $Y$-degree gives the min-weight common basis
-- statement:
--   Let $\mathbb F$ be a finite field, $A,B\in\mathbb F^{N\times m}$, $W\ge0$ and weights $\mathrm{wt}(e)\in[-W,W]$. For $x\in\mathbb F^m$ let $D=\mathrm{diag}(x_eY^{W+\mathrm{wt}(e)})$ and $L=ADB^{T}\in\mathbb F[Y]^{N\times N}$. Write $\alpha_S=\det(A_S)\det(B_S)$.
--
--   1. For every $x$, as Laurent polynomials in $Y$,
--   $$\det(L)=Y^{NW}\sum_{S}\alpha_S\Bigl(\prod_{e\in S}x_e\Bigr)Y^{\sum_{e\in S}\mathrm{wt}(e)},$$
--   the sum over the common bases $S$ ($N$-sets independent in both $A$ and $B$).
--   2. If a common basis exists, then for at least a $1-N/|\mathbb F|$ fraction of $x\in\mathbb F^m$ we have $\det L\ne0$ and $\mathrm{val}_Y(\det L)-NW$ equals the minimum weight of a common basis, where $\mathrm{val}_Y$ is the least exponent with a nonzero coefficient.
--
--   This encoding underlies the weighted oracles of Theorems 3.5 and 3.7.
--
--   Differences from the source:
--   - generalization: M1, M2 rank-N matroids with representations A, B; sum over ℬ(M1) ∩ ℬ(M2) → any A, B ∈ F^{N×m}; sum over the N-sets independent in both; reason: for rank-N matroids these are exactly the common bases; no rank hypothesis is needed
--   - encoding: Y^{NW} … Y^{Σ wt(e)} (negative exponents possible) → the identity in Laurent polynomials (toLaurent, T); D_{e,e} = x_e Y^{(W + wt(e)).toNat}; reason: |wt(e)| ≤ W makes the exponent W + wt(e) a natural number
--   - reading: with the probability 1 − 1/N^{Ω(1)} (F sufficiently large) → when a common basis exists, a fraction ≥ 1 − N/|F| of x ∈ F^m gives det L ≠ 0 and val_Y(det L) − NW = minimum weight; reason: the concrete Schwartz–Zippel bound for a degree-N coefficient; it implies the printed bound for |F| ≥ N^{1+c}; with no common basis det L = 0 and val_Y is undefined
-- source:
--   Choudhary, Kumar, Saggi, Sensitivity Oracles for Matroid Packing, Matroid Covering, and Matching Problems with Applications, arXiv:2609.01283 (held version, sha256 0de50841…), Lemma 3.4, pp.17–18 (PDF pp.20–21), with the setting of §3.2, p.17

import Mathlib
import Definitions.Def_MatroidSensOracle_LinearMatroid

set_option autoImplicit false

open Polynomial

namespace MatroidSensOracle

open Classical in
/-- **Lemma 3.4 (Encoding Common Bases).** Choudhary, Kumar, Saggi, arXiv:2609.01283 (held version,
sha256 0de50841…), pp.17–18 (PDF pp.20–21). Setting (p.17): "Let M1 = (E, ℐ1) and M2 = (E, ℐ2) have
rank N on a common ground set E of size m, with representations A, B ∈ F^{N×m}. […] each element has
an integer weight w(e) ∈ [−W, W] […]. Let Y be an indeterminate, and independently sample a scalar
x_e uniformly from F for each element. Define the diagonal matrix D ∈ F[Y]^{m×m} by setting
D_{e,e} := x_e Y^{W+wt(e)}, D_{e,e′} = 0 (e ≠ e′), and let L be an N × N Laplacian defined as
L := A D B^T. We write val_Y(p) for the least exponent with a nonzero coefficient in a nonzero
polynomial p." Lemma 3.4: "With D as above,
det(L) = Y^{NW} Σ_{S∈ℬ(M1)∩ℬ(M2)} α_S (Π_{e∈S} x_e) Y^{Σ_{e∈S} wt(e)}, where α_S := det(A_S) det(B_S).
Moreover, with the probability 1 − 1/N^{Ω(1)}, the minimum degree of Y in det(L) minus NW equals the
weight of a minimum-weight common basis."

**Formalization Note.**
* `ℬ(M1) ∩ ℬ(M2)` is the set of `N`-subsets `S` whose columns are independent in `A` and in `B`
  (`IsCommonBasisM`); for rank-`N` matroids these are the common bases. No rank hypothesis is needed
  for the statement.
* The identity is stated in Laurent polynomials (`toLaurent`, `T`), since `Σ wt(e)` may be negative;
  `Y^{W + wt(e)}` has exponent `(W + wt(e)).toNat = W + wt(e)` because `|wt(e)| ≤ W`.
* The probability clause (stated when a common basis exists; otherwise `det L = 0`): the fraction of
  `x ∈ F^m` for which `det L ≠ 0` and `val_Y(det L) − NW` equals the minimum weight is at least
  `1 − N/|F|`. This is the concrete Schwartz–Zippel bound behind "1 − 1/N^{Ω(1)}" for a
  sufficiently large field (p.6), and implies it when `|F| ≥ N^{1+c}`. -/
theorem lemma_3_4 {F : Type} [Field F] [Fintype F] [DecidableEq F] (N m W : ℕ)
    (A B : Matrix (Fin N) (Fin m) F) (wt : Fin m → ℤ) (hwt : ∀ e, |wt e| ≤ W) :
    let L : (Fin m → F) → Matrix (Fin N) (Fin N) F[X] := fun x =>
      A.map C * Matrix.diagonal (fun e => C (x e) * X ^ ((W : ℤ) + wt e).toNat) * (B.map C).transpose
    (∀ x : Fin m → F,
      toLaurent (L x).det =
        LaurentPolynomial.T ((N : ℤ) * W) *
          ∑ S ∈ Finset.univ.filter (fun S : {S : Finset (Fin m) // S.card = N} =>
              IsCommonBasisM A B S.1),
            LaurentPolynomial.C ((colSub A S.1 S.2).det * (colSub B S.1 S.2).det * ∏ e ∈ S.1, x e) *
              LaurentPolynomial.T (∑ e ∈ S.1, wt e)) ∧
    ((∃ S, IsCommonBasisM A B S) →
      1 - (N : ℝ) / Fintype.card F ≤
        ((Finset.univ.filter fun x : Fin m → F => (L x).det ≠ 0 ∧
            ((((L x).det.natTrailingDegree : ℤ) - (N : ℤ) * W : ℤ) : WithTop ℤ) =
              minCommonBasisWeightM A B wt).card : ℝ) / Fintype.card (Fin m → F)) := by sorry

end MatroidSensOracle
