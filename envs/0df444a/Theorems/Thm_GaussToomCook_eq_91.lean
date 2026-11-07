-- Prove2me | Theorems.Thm_GaussToomCook_eq_91
-- name    : GaussToomCook.eq_91
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:46:10.404657+00:00
-- url     : https://prove2.me/theorems/a58ea00d-7c10-4638-9d6a-be61278ad6de
-- title:
--   Eq. (91) — $e_1\cdots e_n$ is the gcd of the $n\times n$ minors
-- statement:
--   Let $R$ be a principal ideal domain and $A$ an $N\times N$ matrix over $R$ with elementary divisors $e_1\mid e_2\mid\cdots\mid e_N$ (the diagonal of a Smith normal form). For every $n\le N$, the product of the first $n$ elementary divisors is, up to a unit, the greatest common divisor of all $n\times n$ minors:
--   $$e_1\cdots e_n=\epsilon\cdot\gcd_{\substack{T,\ \mathcal J\\ |T|=|\mathcal J|=n}}\det A[T;\mathcal J],\qquad \epsilon\in R^\times ,$$
--   where $T$ ranges over sets of $n$ rows and $\mathcal J$ over sets of $n$ columns. Equivalently, an element $c\in R$ divides every $n\times n$ minor of $A$ if and only if $c\mid e_1\cdots e_n$.
--
--   In the paper this is applied to $A=V(S)$ over $\mathbb Z[i]$, whose minors are the matrices $V(T;\mathcal J)=[x^jy^{2k-2-j}]_{(x,y)\in T,\,j\in\mathcal J}$ of eq. (90).
--
--   Differences from the source:
--   - generalization: A = V(S) over ℤ[i], n = 1, …, 2k − 1 → any N × N matrix over any principal ideal domain, every n ≤ N; reason: [Bos09, Satz 6] is the general statement; V(S) over ℤ[i] is an instance and n = 0 is the trivial case 1 = 1.
--   - encoding: e₁ ⋯ e_n = ε · gcd of the n × n minors → c divides every minor det (A.submatrix f g) (f, g strictly increasing) iff c ∣ prefixProd d n, for every c; reason: two elements with the same common divisors with a family are associated; no GCDMonoid instance is needed, and strictly increasing f, g enumerate the subsets T, 𝒥.
--   - encoding: the elementary divisors e₁ | e₂ | ⋯ of a matrix → the diagonal d of any Smith normal form U A V = diag(d) with U, V of unit determinant and d i ∣ d j for i ≤ j (IsSmithNF); reason: over a PID the form exists and d is unique up to units, so a statement for every such d is a statement about the elementary divisors.
-- source:
--   Y. Spiizer, R. S. Steiner, Rational and Gaussian long integer multiplication, manuscript (STOC 2027 submission; held version sha256 f50b53628a53a03bd55785424af241d0ac5ea751714330838e4017b90b27ad70), §9.3, proof of Proposition 9.5, eq. (91), p. 31 (PDF p. 33), citing [Bos09, Satz 6, p. 77]

import Mathlib
import Definitions.Def_GaussToomCook_IsSmithNF

namespace GaussToomCook

/-- **Eq. (91): products of elementary divisors are gcds of minors**, Spiizer, Steiner, *Rational and
Gaussian long integer multiplication*, manuscript (STOC 2027 submission; sha256 f50b5362…27ad70), §9.3,
proof of Proposition 9.5, p. 31 (PDF 33), citing [Bos09, Satz 6, p. 77].

Let `R` be a principal ideal domain, `A` an `N × N` matrix over `R` with Smith normal form
`U A V = diag(d)`, `d 0 ∣ d 1 ∣ ⋯`. For every `n ≤ N`, an element `c` divides every `n × n` minor of `A`
if and only if it divides `d 0 ⋯ d (n−1)`; i.e. `e₁ ⋯ e_n` is associated to the gcd of the `n × n` minors.

**Formalization Note.** The `n × n` minors are `det (A.submatrix f g)` for strictly increasing row and
column selections `f g : Fin n → Fin N` (the subsets `T ⊆ S`, `J ⊆ {0, …, 2k−2}` of (91)). "Associated to the
gcd" is stated as "has the same common divisors as all the minors", which needs no `GCDMonoid`. -/
theorem eq_91 {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] {N : ℕ}
    (A U V : Matrix (Fin N) (Fin N) R) (d : Fin N → R) (hA : IsSmithNF A U V d)
    (n : ℕ) (hn : n ≤ N) (c : R) :
    (∀ f g : Fin n → Fin N, StrictMono f → StrictMono g → c ∣ (A.submatrix f g).det) ↔
      c ∣ prefixProd d n := by sorry

end GaussToomCook
