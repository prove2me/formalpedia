-- Prove2me | Theorems.Thm_GaussToomCook_Supplement_theorem_3_1
-- name    : GaussToomCook.Supplement.theorem_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T23:55:35.775562+00:00
-- url     : https://prove2.me/theorems/059af0f5-5d60-4c9c-acf1-e91e53657dad
-- title:
--   Theorem 3.1 — the rational-to-Gaussian Toom–Cook reduction is well-defined and correct
-- statement:
--   Let $k\ge1$ and let $T=R\sqcup S\sqcup\overline S$ be a set of $2k-1$ evaluation points in $\mathbb Z[i]^2\setminus\{(0,0)\}$ that project onto $2k-1$ distinct points of $\mathbb P^1(\mathbb Q(i))$, where $R\subset\mathbb Z^2\setminus\{(0,0)\}$ consists of $r$ rational points, $S$ of $s$ purely Gaussian points (projections in $\mathbb P^1(\mathbb Q(i))\setminus\mathbb P^1(\mathbb Q)$) and $\overline S$ of their complex conjugates, $r+2s=2k-1$. Let $a,b\in\mathbb Z$, $M\in\mathbb Z_{>0}$ and rational-integer parts with
--   $$a=\sum_{j=0}^{k-1}[a]_jM^j,\qquad b=\sum_{j=0}^{k-1}[b]_jM^j,$$
--   let $P_1,P_2\in\mathbb Z[X,Y]$ be the polynomials $\sum_j[a]_jX^jY^{k-1-j}$, $\sum_j[b]_jX^jY^{k-1-j}$, and $Q=P_1P_2=\sum_{j=0}^{2k-2}q_jX^jY^{2k-2-j}$. The reduction computes $Q(\rho)=P_1(\rho)P_2(\rho)$ for $\rho\in R$ and $Q(\sigma)=P_1(\sigma)P_2(\sigma)$ for $\sigma\in S$ only, and uses $\overline{Q(\sigma)}$ as the value at $\overline\sigma$. Then the reduction is well-defined and correct:
--
--   1. the interpolation system of step (VI),
--   $$\sum_{j=0}^{2k-2}x^jy^{2k-2-j}c_j=\begin{cases}Q(x,y)&(x,y)\in R\sqcup S,\\ \overline{Q(\sigma)}&(x,y)=\overline\sigma\in\overline S,\end{cases}$$
--   whose matrix is the Vandermonde matrix $V(T)$, has exactly one solution $c$, namely $c=(q_0,\dots,q_{2k-2})$;
--   2. the value returned in step (VII) is the product: $\sum_{j=0}^{2k-2}q_jM^j=a\cdot b$.
--
--   The theorem shows that a product of rational integers can be computed from Gaussian products at the points of $S$ and rational products at the points of $R$ only, with the conjugate points coming for free.
--
--   **Formalization Note** $T$ is a family indexed by `Fin (2k − 1)` satisfying the published `IsEvalPoints`, split into $R$, $S$, $\overline S$ by a bijection `Fin r ⊕ (Fin s ⊕ Fin s) ≃ Fin (2k − 1)`; conjugation on $\mathbb Z[i]$ is `star`. The system is solved over $\mathbb C$, with $\mathbb Z[i]$ and $\mathbb Z$ embedded.
--
--   Differences from the source:
--   - reading: "well-defined and correct" → the interpolation system of (VI) with conjugated values on $\overline S$ has the coefficient vector of $Q$ as its unique solution, and $\sum_j q_jM^j=a\cdot b$; reason: this is what the paper's justification before the theorem (p. 9) establishes, and nothing else in the scheme can fail
--   - generalization: the system solved over $\mathbb Q(i)$ → candidate solutions range over $\mathbb C$; reason: the matrix remains invertible after the scalar extension $\mathbb Q(i)\hookrightarrow\mathbb C$, so the stronger uniqueness statement specializes to the source
--   - encoding: products in (IV)/(V) computed by a Gaussian multiplication algorithm or recursively → exact products in $\mathbb Z[i]$ and $\mathbb Z$; reason: correctness depends only on the values computed, not on how
--   - encoding: the set $T=R\sqcup S\sqcup\overline S$ → a family indexed by `Fin (2k − 1)` with a bijection from `Fin r ⊕ (Fin s ⊕ Fin s)`; reason: pairwise non-proportionality makes the indexing injective, and the bijection forces $r+2s=2k-1$
--   - encoding: $S$ purely Gaussian ($x\bar y-\bar xy\ne0$) as a hypothesis → not a separate hypothesis; reason: it is exactly the non-proportionality of $\sigma$ and $\overline\sigma$, both points of $T$, which `IsEvalPoints` already requires
-- source:
--   Y. Spiizer, R. S. Steiner, Rational and Gaussian long integer multiplication, manuscript (STOC 2027 submission; held version sha256 f50b53628a53a03bd55785424af241d0ac5ea751714330838e4017b90b27ad70), §3, Theorem 3.1, p. 9 (PDF p. 11); setting and steps (I)–(VII), pp. 8–9 (PDF pp. 10–11)

import Mathlib
import Definitions.Def_GaussToomCook_IsEvalPoints
import Definitions.Def_GaussToomCook_vandMatrix
import Definitions.Def_GaussToomCook_Supplement_tcPoly

namespace GaussToomCook.Supplement

open MvPolynomial

/-- **Theorem 3.1** (the rational-to-Gaussian Toom–Cook reduction is well-defined and correct), Spiizer, Steiner,
*Rational and Gaussian long integer multiplication*, manuscript (STOC 2027 submission; sha256 f50b5362…27ad70),
§3, pp. 8–9 (PDF 10–11): "The Toom–Cook rational-to-Gaussian integer multiplication reduction scheme is
well-defined and correct."

Let `k ≥ 1` and let `T = R ⊔ S ⊔ S̄` be `2k − 1` evaluation points (`IsEvalPoints`), where `R` consists of `r`
rational points `(u, v) ∈ ℤ² \ {(0,0)}`, `S` of `s` purely Gaussian points, and `S̄` of their complex conjugates
(`r + 2s = 2k − 1`). Let `M ∈ ℤ_{>0}`, `a = ∑ [a]_j M^j`, `b = ∑ [b]_j M^j` with rational-integer parts (1), and
`P₁, P₂ ∈ ℤ[X, Y]` as in (2), `Q = P₁ · P₂`. Values are computed only at `R ⊔ S` (steps (III)–(V)); at the
point `σ̄` the value used is the complex conjugate of the value computed at `σ`. Then
1. the interpolation system of step (VI), with rows of `V(T)` and right-hand side `Q(ρ)` at `ρ ∈ R`, `Q(σ)` at
   `σ ∈ S`, `conj Q(σ)` at `σ̄ ∈ S̄`, has exactly one solution, namely the coefficient vector of `Q`;
2. the value returned in step (VII), `∑_j q_j M^j = Q(M, 1)`, equals `a · b`.

**Formalization Note.** `T` is a family indexed by `Fin (2k − 1)`, split by the bijection
`e : Fin r ⊕ (Fin s ⊕ Fin s) ≃ Fin (2k − 1)`; complex conjugation on `ℤ[i]` is `star`. That the `S`-points are
purely Gaussian (projection in `P¹(ℚ(i)) \ P¹(ℚ)`, i.e. `x ȳ − x̄ y ≠ 0`) is not a separate hypothesis: it is
exactly the non-proportionality of `σ` and `σ̄`, both points of `T`, which `IsEvalPoints k T` already asserts.
The system is solved over `ℂ`; uniqueness over `ℂ` implies uniqueness over `ℚ(i)`. -/
theorem theorem_3_1 (k : ℕ) (hk : 0 < k) (r s : ℕ) (e : Fin r ⊕ (Fin s ⊕ Fin s) ≃ Fin (2 * k - 1))
    (T : Fin (2 * k - 1) → GaussianInt × GaussianInt) (hT : GaussToomCook.IsEvalPoints k T)
    (R : Fin r → ℤ × ℤ) (S : Fin s → GaussianInt × GaussianInt)
    (hR : ∀ i, T (e (Sum.inl i)) = (((R i).1 : GaussianInt), ((R i).2 : GaussianInt)))
    (hS : ∀ i, T (e (Sum.inr (Sum.inl i))) = S i)
    (hSbar : ∀ i, T (e (Sum.inr (Sum.inr i))) = (star (S i).1, star (S i).2))
    (M : ℤ) (hM : 0 < M) (a b : ℤ) (A B : Fin k → ℤ)
    (ha : a = ∑ j : Fin k, A j * M ^ (j : ℕ)) (hb : b = ∑ j : Fin k, B j * M ^ (j : ℕ)) :
    (∀ c : Fin (2 * k - 1) → ℂ,
        (∀ x : Fin r ⊕ (Fin s ⊕ Fin s),
            ∑ j, GaussianInt.toComplex (GaussToomCook.vandMatrix k T (e x) j) * c j =
              match x with
              | Sum.inl i =>
                  ((eval ![(R i).1, (R i).2] (tcPoly k A) *
                      eval ![(R i).1, (R i).2] (tcPoly k B) : ℤ) : ℂ)
              | Sum.inr (Sum.inl i) =>
                  GaussianInt.toComplex
                    (aeval ![(S i).1, (S i).2] (tcPoly k A) * aeval ![(S i).1, (S i).2] (tcPoly k B))
              | Sum.inr (Sum.inr i) =>
                  starRingEnd ℂ (GaussianInt.toComplex
                    (aeval ![(S i).1, (S i).2] (tcPoly k A) *
                      aeval ![(S i).1, (S i).2] (tcPoly k B)))) ↔
          ∀ j, c j = ((prodCoeff k A B j : ℤ) : ℂ)) ∧
      ∑ j : Fin (2 * k - 1), prodCoeff k A B j * M ^ (j : ℕ) = a * b := by sorry

end GaussToomCook.Supplement
