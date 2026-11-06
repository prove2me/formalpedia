-- Prove2me | Theorems.Thm_NewtonLCP_lemma_8_3
-- name    : NewtonLCP.lemma_8_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:29:43.950399+00:00
-- url     : https://prove2.me/theorems/16b43075-1e23-4c82-883e-5228bc4be0c6
-- title:
--   Lemma 8.3 — basic feasible solutions have coordinates in $\{0\}\cup[1/\Delta,\Delta]$, $\Delta\le2^{O(L)}$
-- statement:
--   Let $M\in\mathbb Q^{n\times n}$, $q\in\mathbb Q^n$, and let $L$ be the total encoding length of $(M,q)$. Then there exists an integer $\Delta\le2^{O(L)}$ such that $\|M\|_{\max}+\|q\|_\infty\le\Delta$ and, for every basic feasible solution $(x,s)$ of the polyhedron $\mathcal F(M,q)$ and every $i\in[n]$,
--
--   $$x_i,\ s_i\in\{0\}\cup[1/\Delta,\Delta].$$
--
--   This standard bit-complexity bound (cited from [Sch98]) fixes the scale $\Delta$ of the initialization (52) and the final accuracy $\mu_1$.
--
--   **Formalization Note** $2^{O(L)}$ is $2^{C\cdot L}$ with one constant $C$ for all $n,M,q$. The property of $\Delta$ is the definition of a bit bound.
--
--   Differences from the source:
--   - encoding: Δ ≤ 2^{O(L)} → ∃ C : ℕ before all n, M, q with Δ ≤ 2^{C·L}; reason: O(·) is one constant uniform in the instance; L ≥ 2 whenever n ≥ 1, so a multiplicative constant absorbs additive ones
--   - encoding: basic feasible solution of F(M, q) → extreme point of F(M, q) ⊆ ℝ²ⁿ; reason: for a polyhedron the two notions coincide
--   - reading: Δ ∈ ℤ with coordinates in [1/Δ, Δ] → Δ ∈ ℤ with 1 ≤ Δ stated; reason: the interval [1/Δ, Δ] presupposes Δ > 0, i.e. Δ ≥ 1 for an integer
--   - encoding: total encoding length L → Σ bitSize of the entries of M and q; reason: any standard encoding is within constant factors
-- source:
--   Ma–Végh–Vladu, Newton Steps are Faster for Linear Complementarity Problems, STOC 2027 submission (manuscript sha256 a70e5eab…), Lemma 8.3, p.29 (cited)

import Mathlib
import Definitions.Def_NewtonLCP_Encoding
import Definitions.Def_NewtonLCP_BitBound

namespace NewtonLCP

/-- **Lemma 8.3** (bit-complexity bound). Ma–Végh–Vladu, *Newton Steps are Faster for Linear Complementarity Problems*, STOC 2027
submission manuscript (sha256 a70e5eab52f43bef42b49a8833f8d0483556c18b939405dba6bc1e25ea0740f8), Lemma 8.3, p.29 (cited from [Sch98]; not proved
in the paper).

Let `M ∈ ℚⁿˣⁿ`, `q ∈ ℚⁿ` and `L` the total encoding length of `(M, q)`. Then there exists
`∆ ≤ 2^{O(L)}`, `∆ ∈ ℤ`, such that `‖M‖_max + ‖q‖_∞ ≤ ∆`, and for every basic feasible solution
`(x, s)` of the polyhedron `F(M, q)` and every `i ∈ [n]`, `xᵢ, sᵢ ∈ {0} ∪ [1/∆, ∆]`.

**Formalization Note.** `2^{O(L)}` is `2^{C·L}` with one constant `C` for all `n, M, q` (chosen
before them); `L = encLen M q`. The property after "such that" is `IsBitBound` (basic feasible
solutions are extreme points of `F(M, q)`; `1 ≤ ∆` is made explicit). -/
theorem lemma_8_3 : ∃ C : ℕ, ∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℚ) (q : Fin n → ℚ),
    ∃ Δ : ℤ, (Δ : ℝ) ≤ 2 ^ (C * encLen M q) ∧
      IsBitBound (M.map ((↑) : ℚ → ℝ)) (fun i => (q i : ℝ)) Δ := by sorry

end NewtonLCP
