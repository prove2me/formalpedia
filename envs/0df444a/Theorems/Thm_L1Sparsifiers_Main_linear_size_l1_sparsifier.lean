-- Prove2me | Theorems.Thm_L1Sparsifiers_Main_linear_size_l1_sparsifier
-- name    : L1Sparsifiers.Main.linear_size_l1_sparsifier
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:06:13.883625+00:00
-- url     : https://prove2.me/theorems/5a44a335-a5cd-4085-8e49-d5d5e3f3c254
-- title:
--   Theorem 1 — linear-size $\ell_1$ sparsifiers: $O(n/\varepsilon^2)$ nonnegative row weights preserve $\|Ax\|_1$ within $1\pm\varepsilon$
-- statement:
--   There is an absolute constant $C>0$ such that for all $m,n\in\mathbb N$, every matrix $A\in\mathbb R^{m\times n}$ and every $0<\varepsilon\le1$ there is a diagonal matrix $D=\mathrm{diag}(w)$ with $w\in\mathbb R^m_{\ge0}$ and at most $C\,n/\varepsilon^2$ nonzero entries such that
--   $$(1-\varepsilon)\|Ax\|_1\le\|DAx\|_1\le(1+\varepsilon)\|Ax\|_1\qquad\text{for all }x\in\mathbb R^n .$$
--   Here $\|Ax\|_1=\sum_{i=1}^m|(Ax)_i|$ and $\|DAx\|_1=\sum_i|w_i(Ax)_i|$. A single $w$ works for every $x$; no assumption on the rank, entries or number of rows of $A$ is made.
--
--   The bound $O(n/\varepsilon^2)$ removes the $\log n$ factor of Talagrand's 1990 bound and matches the lower bound for cut sparsifiers. Equivalently, every zonotope in $\mathbb R^n$ is $(1\pm\varepsilon)$-approximated by a reweighting of $O(n/\varepsilon^2)$ of its own generators.
--
--   Differences from the source:
--   - encoding: a diagonal D ∈ ℝ^{m×m}_{≥0} with at most O(n/ε²) nonzero entries → a weight vector w ≥ 0 (D = diag w) with #{i : w_i ≠ 0} ≤ C n/ε² for one C > 0 chosen before m, n, A, ε; reason: diag(w) is exactly a nonnegative diagonal matrix, and O(·) with an absolute constant means a uniform C
-- source:
--   Victor Reis, Thomas Rothvoss, Linear-size ℓ1 sparsifiers, STOC 2027 submission #162 (October 2026; PDF SHA-256 5137e7dee3cd303bd508f90f5f42c955632af5dc2ec978d9ef575bae4ce23710), §1.1, Theorem 1, p.3

import Mathlib

namespace L1Sparsifiers.Main

/-- **Theorem 1** (Reis–Rothvoss, *Linear-size ℓ1 sparsifiers*, STOC 2027 submission #162, p.3).
"For any matrix A ∈ ℝ^{m×n} and any 0 < ε ≤ 1, there is a diagonal matrix D ∈ ℝ^{m×m}_{≥0} with at
most O(n/ε²) nonzero entries so that (1 − ε)‖Ax‖₁ ≤ ‖DAx‖₁ ≤ (1 + ε)‖Ax‖₁ ∀x ∈ ℝⁿ."

`D = diag(w)`. There is one absolute constant `C > 0` (chosen before `m, n, A, ε`) such that the
weights `w ≥ 0` have at most `C n / ε²` nonzero entries, and one `w` works for every `x`. -/
theorem linear_size_l1_sparsifier :
    ∃ C : ℝ, 0 < C ∧
      ∀ (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℝ) (ε : ℝ), 0 < ε → ε ≤ 1 →
        ∃ w : Fin m → ℝ, (∀ i, 0 ≤ w i) ∧
          ((Finset.univ.filter (fun i => w i ≠ 0)).card : ℝ) ≤ C * n / ε ^ 2 ∧
          ∀ x : Fin n → ℝ,
            (1 - ε) * ∑ i, |(A.mulVec x) i| ≤ ∑ i, |w i * (A.mulVec x) i| ∧
            ∑ i, |w i * (A.mulVec x) i| ≤ (1 + ε) * ∑ i, |(A.mulVec x) i| := by sorry

end L1Sparsifiers.Main
