-- Prove2me | Theorems.Thm_LPAllocRM_g_tendstoUniformlyOn
-- name    : LPAllocRM.g_tendstoUniformlyOn
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:05:09.601987+00:00
-- url     : https://prove2.me/theorems/6076f82c-8d5d-499a-b8e5-53d6ff68e274
-- title:
--   $g_k(y)=\sum_j f_j(y_j\wedge k^{-1}\lfloor kx^*_j\rfloor)\to\sum_j f_j(y_j\wedge x^*_j)$ uniformly on compacts
-- statement:
--   For a fare vector $f$ and a vector $x^*\in\mathbb R^n$ define, for $k=1,2,\dots$,
--
--   $$g_k(y)\equiv\sum_{j=1}^n f_j\bigl(y_j\wedge k^{-1}\lfloor kx^*_j\rfloor\bigr),\qquad g(y)\equiv\sum_{j=1}^n f_j\bigl(y_j\wedge x^*_j\bigr),\qquad y\in\mathbb R^n,$$
--
--   where $\lfloor r\rfloor$ is the largest integer not exceeding $r$. Then $g$ is continuous, and $g_k\to g$ uniformly on every compact subset of $\mathbb R^n$.
--
--   Since $k^{-1}R^{LP(k)}=g_k(k^{-1}D^{(k)}(\tau))$, this is what lets Lemma 1 carry (7) to the normalized revenue in Proposition 1.
--
--   Differences from the source:
--   - generalization: x* an optimal solution of (3) and f the fare vector of the model → every f ∈ ℝ^n and every x* ∈ ℝ^n; reason: the convergence holds for every real vector; it specializes to the paper's x*
--   - encoding: problems k = 1, 2, … (k ⩾ 1) → k : ℕ+, limits along atTop on ℕ+; reason: same index set; there is no problem k = 0
-- source:
--   Cooper, Asymptotic Behavior of an Allocation Policy for Revenue Management, Operations Research 50(4) (2002), doi:10.1287/opre.50.4.720.2855, proof of Proposition 1, p.724

import Mathlib
open Filter

namespace LPAllocRM

/-- The functions `g_k(y) ≡ ∑_j f_j (y_j ∧ k^{-1}⌊k x*_j⌋)` converge uniformly on compact sets to the
continuous function `g(y) ≡ ∑_j f_j (y_j ∧ x*_j)` as `k → ∞`.
Cooper, *Asymptotic Behavior of an Allocation Policy for Revenue Management*, Operations Research 50(4) (2002), doi:10.1287/opre.50.4.720.2855,
proof of Proposition 1, p.724 (PDF p.5).

**Formalization Note** `⌊·⌋` is the integer floor `Int.floor`, the paper's `⌊r⌋ ≡ max{i ∈ ℤ : i ⩽ r}`
(p.723). The claim is stated for every fare vector `f` and every real vector `x*`; the paper's `x*`
is an optimal solution of (3). -/
theorem g_tendstoUniformlyOn {n : ℕ} (f : Fin n → ℝ) (xstar : Fin n → ℝ) :
    Continuous (fun y : Fin n → ℝ => ∑ j, f j * min (y j) (xstar j)) ∧
      ∀ K : Set (Fin n → ℝ), IsCompact K →
        TendstoUniformlyOn
          (fun (k : ℕ+) (y : Fin n → ℝ) =>
            ∑ j, f j * min (y j) (((k : ℕ) : ℝ)⁻¹ * (⌊((k : ℕ) : ℝ) * xstar j⌋ : ℝ)))
          (fun y : Fin n → ℝ => ∑ j, f j * min (y j) (xstar j)) atTop K := by sorry

end LPAllocRM
