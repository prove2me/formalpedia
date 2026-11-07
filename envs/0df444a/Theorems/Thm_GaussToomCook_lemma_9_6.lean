-- Prove2me | Theorems.Thm_GaussToomCook_lemma_9_6
-- name    : GaussToomCook.lemma_9_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:46:09.845223+00:00
-- url     : https://prove2.me/theorems/6dda7b96-dc1e-42c7-bda9-18e480e705e5
-- title:
--   Lemma 9.6 — $\prod_{j\le i}e_j(L:M)\cdot\prod_{j\le i}e_j(M:N)$ divides $\prod_{j\le i}e_j(L:N)$
-- statement:
--   Let $R$ be a principal ideal domain and $L\subseteq M\subseteq N$ free $R$-modules of equal rank $n$. Fix bases; let $A$ be the matrix expressing the basis of $L$ in that of $M$, $B$ the matrix expressing the basis of $M$ in that of $N$, so that $C=AB$ expresses the basis of $L$ in that of $N$. Write $e_j(L:M)$, $e_j(M:N)$, $e_j(L:N)$ for the elementary divisors of $A$, $B$, $C$, i.e. of the inclusions. Then for $i=1,\dots,n$
--   $$\prod_{j=1}^{i}e_j(L:M)\cdot\prod_{j=1}^{i}e_j(M:N)\ \Big|\ \prod_{j=1}^{i}e_j(L:N).$$
--
--   Applied to $\Lambda_0\subseteq\Lambda\subseteq\Lambda_N$ in the proof of Proposition 9.4, it shows that $\Lambda_0\subseteq\Lambda_N$ has at least as many elementary divisors divisible by $p$ as $\Lambda_0\subseteq\Lambda$, i.e. as $V(S)$.
--
--   Differences from the source:
--   - encoding: free submodules L ⊆ M ⊆ N of equal rank n and their elementary divisors → matrices A, B over R with det A ≠ 0, det B ≠ 0, C = A * B, and the diagonals of any Smith normal forms of A, B, A * B; reason: the paper's proof works with these matrices (rows = basis vectors, so C = AB); every such chain gives such A, B, and every such A, B arise from the chain rowspace(AB) ⊆ rowspace(B) ⊆ Rⁿ.
--   - generalization: i = 1, …, n → every i ≤ n; reason: i = 0 is the trivial 1 · 1 ∣ 1.
--   - encoding: the elementary divisors e₁ | e₂ | ⋯ of a matrix → the diagonal d of any Smith normal form U A V = diag(d) with U, V of unit determinant and d i ∣ d j for i ≤ j (IsSmithNF); reason: over a PID the form exists and d is unique up to units, so a statement for every such d is a statement about the elementary divisors.
-- source:
--   Y. Spiizer, R. S. Steiner, Rational and Gaussian long integer multiplication, manuscript (STOC 2027 submission; held version sha256 f50b53628a53a03bd55785424af241d0ac5ea751714330838e4017b90b27ad70), §9.3, Lemma 9.6, eq. (94), p. 32 (PDF p. 34)

import Mathlib
import Definitions.Def_GaussToomCook_IsSmithNF

namespace GaussToomCook

/-- **Lemma 9.6: product inequality for elementary divisors**, Spiizer, Steiner, *Rational and
Gaussian long integer multiplication*, manuscript (STOC 2027 submission; sha256 f50b5362…27ad70), §9.3,
p. 32 (PDF 34).

Let `R` be a principal ideal domain and `L ⊆ M ⊆ N` free `R`-modules of equal rank `n`. Write `A` for the
matrix expressing a basis of `L` in a basis of `M`, `B` for that of `M` in `N`, so that `C = A B` expresses
the basis of `L` in that of `N`. If `dA`, `dB`, `dC` are the elementary divisors of `A`, `B`, `C`
(`e_j(L : M)`, `e_j(M : N)`, `e_j(L : N)`), then for `i = 1, …, n`
`∏_{j ≤ i} e_j(L : M) · ∏_{j ≤ i} e_j(M : N) ∣ ∏_{j ≤ i} e_j(L : N)`.

**Formalization Note.** Matrix form, as in the paper's proof ("Let C be the matrix expressing …,
C = AB"): basis vectors are rows, so `l = A m` and `m = B n` give `C = A * B`. Equal rank means `A`, `B`
nonsingular. Elementary divisors are the diagonals of any Smith normal forms with divisibility chain;
`prefixProd d i` is the product of the first `i` of them (`i = 0` is included and trivial). -/
theorem lemma_9_6 {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) R) (hA : A.det ≠ 0) (hB : B.det ≠ 0)
    (UA VA UB VB UC VC : Matrix (Fin n) (Fin n) R) (dA dB dC : Fin n → R)
    (hdA : IsSmithNF A UA VA dA) (hdB : IsSmithNF B UB VB dB) (hdC : IsSmithNF (A * B) UC VC dC)
    (i : ℕ) (hi : i ≤ n) :
    prefixProd dA i * prefixProd dB i ∣ prefixProd dC i := by sorry

end GaussToomCook
