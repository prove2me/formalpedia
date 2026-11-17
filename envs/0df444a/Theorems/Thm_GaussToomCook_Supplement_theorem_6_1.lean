-- Prove2me | Theorems.Thm_GaussToomCook_Supplement_theorem_6_1
-- name    : GaussToomCook.Supplement.theorem_6_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T23:56:06.083097+00:00
-- url     : https://prove2.me/theorems/7dc85b13-596f-422f-b4c0-adc5171eabe3
-- title:
--   Theorem 6.1 — Gaussian Toom–Cook-$k$ is well-defined and correct
-- statement:
--   Let $k\ge1$ and let $S\subset\mathbb Z[i]^2\setminus\{(0,0)\}$ be a set of $2k-1$ pairs that project onto $2k-1$ distinct points of $\mathbb P^1(\mathbb Q(i))$. Let $a,b\in\mathbb Z[i]$, $M\in\mathbb Z_{>0}$ and parts $[a]_j,[b]_j\in\mathbb Z[i]$ with
--   $$a=\sum_{j=0}^{k-1}[a]_jM^j,\qquad b=\sum_{j=0}^{k-1}[b]_jM^j,$$
--   let $P_1=\sum_j[a]_jX^jY^{k-1-j}$, $P_2=\sum_j[b]_jX^jY^{k-1-j}$ and $Q=P_1P_2=\sum_{j=0}^{2k-2}q_jX^jY^{2k-2-j}$. Then the Gaussian Toom–Cook-$k$ scheme is well-defined and correct:
--
--   1. the interpolation system of step (V),
--   $$\sum_{j=0}^{2k-2}x^jy^{2k-2-j}c_j=P_1(x,y)\,P_2(x,y),\qquad (x,y)\in S,$$
--   whose matrix is the Vandermonde matrix $V(S)$, has exactly one solution $c$, namely $c=(q_0,\dots,q_{2k-2})$;
--   2. the value returned in step (VI) is the product: $\sum_{j=0}^{2k-2}q_jM^j=a\cdot b$.
--
--   This is the correctness statement underlying every Gaussian Toom–Cook-$k$ algorithm whose interpolation phase is analysed in §9 and §10.
--
--   **Formalization Note** $S$ is a family indexed by `Fin (2k − 1)` satisfying the published `IsEvalPoints`, and $V(S)$ is the published `vandMatrix`. The system is solved over $\mathbb C$, with $\mathbb Z[i]$ embedded by `GaussianInt.toComplex`.
--
--   Differences from the source:
--   - reading: "well-defined and correct" → the interpolation system of (V) has the coefficient vector of $Q$ as its unique solution, and $\sum_j q_jM^j=a\cdot b$; reason: this is what the paper's justification before the theorem (p. 13) establishes, and nothing else in the scheme can fail
--   - generalization: the system solved over $\mathbb Q(i)$ → candidate solutions range over $\mathbb C$; reason: the matrix remains invertible after the scalar extension $\mathbb Q(i)\hookrightarrow\mathbb C$, so the stronger uniqueness statement specializes to the source
--   - encoding: products in (IV) computed directly or recursively → exact products in $\mathbb Z[i]$; reason: correctness depends only on the values computed, not on how
--   - encoding: the set $S$ of $2k-1$ points → a family indexed by `Fin (2k − 1)`; reason: pairwise non-proportionality makes the indexing injective
-- source:
--   Y. Spiizer, R. S. Steiner, Rational and Gaussian long integer multiplication, manuscript (STOC 2027 submission; held version sha256 f50b53628a53a03bd55785424af241d0ac5ea751714330838e4017b90b27ad70), §6, Theorem 6.1, p. 13 (PDF p. 15); setting and steps (I)–(VI), p. 13 (PDF p. 15)

import Mathlib
import Definitions.Def_GaussToomCook_IsEvalPoints
import Definitions.Def_GaussToomCook_vandMatrix
import Definitions.Def_GaussToomCook_Supplement_tcPoly

namespace GaussToomCook.Supplement

open MvPolynomial

/-- **Theorem 6.1** (Gaussian Toom–Cook is well-defined and correct), Spiizer, Steiner, *Rational and Gaussian long
integer multiplication*, manuscript (STOC 2027 submission; sha256 f50b5362…27ad70), §6, p. 13 (PDF 15):
"The Gaussian Toom–Cook integer multiplication scheme is well-defined and correct."

Let `k ≥ 1`, let `S` be `2k − 1` evaluation points (`IsEvalPoints`), `M ∈ ℤ_{>0}`, and `a = ∑ [a]_j M^j`,
`b = ∑ [b]_j M^j` with parts in `ℤ[i]` (7). With `P₁, P₂` as in (8) and `Q = P₁ · P₂`:
1. the interpolation system of step (V), `V(S) c = (P₁(x,y) · P₂(x,y))_{(x,y) ∈ S}`, has exactly one solution,
   namely the coefficient vector `(q_0, …, q_{2k−2})` of `Q`;
2. the value returned in step (VI), `∑_j q_j M^j = Q(M, 1)`, equals `a · b`.

**Formalization Note.** The linear system is solved over `ℂ` (entries of `V(S)` and the right-hand side mapped
by `GaussianInt.toComplex`); uniqueness over `ℂ` implies uniqueness over `ℚ(i)`. The pointwise products of
step (IV) are modelled as exact products in `ℤ[i]` (the recursion is irrelevant to correctness). -/
theorem theorem_6_1 (k : ℕ) (hk : 0 < k) (S : Fin (2 * k - 1) → GaussianInt × GaussianInt)
    (hS : GaussToomCook.IsEvalPoints k S) (M : ℤ) (hM : 0 < M) (a b : GaussianInt)
    (A B : Fin k → GaussianInt) (ha : a = ∑ j : Fin k, A j * (M : GaussianInt) ^ (j : ℕ))
    (hb : b = ∑ j : Fin k, B j * (M : GaussianInt) ^ (j : ℕ)) :
    (∀ c : Fin (2 * k - 1) → ℂ,
        (∀ r, ∑ j, GaussianInt.toComplex (GaussToomCook.vandMatrix k S r j) * c j =
            GaussianInt.toComplex
              (eval ![(S r).1, (S r).2] (tcPoly k A) * eval ![(S r).1, (S r).2] (tcPoly k B))) ↔
          ∀ j, c j = GaussianInt.toComplex (prodCoeff k A B j)) ∧
      ∑ j : Fin (2 * k - 1), prodCoeff k A B j * (M : GaussianInt) ^ (j : ℕ) = a * b := by sorry

end GaussToomCook.Supplement
