-- Prove2me | Theorems.Thm_FourierRankQLB_lemma_3_4
-- name    : FourierRankQLB.lemma_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:43:37.585841+00:00
-- url     : https://prove2.me/theorems/6e06efa1-e5db-488f-8b60-1ad2c9a043ec
-- title:
--   Lemma 3.4 — reflection orthogonality
-- statement:
--   Let $n\ge1$. If $\operatorname{rank}\Xi<n$, then
--   $$
--   \int_{O(n)}\det(Q)\,\chi_\Xi(Q)\,d\mu_n(Q)=0 .
--   $$
--   Consequently, $Q\mapsto\det Q$ is orthogonal to $V_{n-1}^{(n)}$, and
--   $$
--   \int_{O(n)}\det(Q)\,f(Q)\,d\mu_n(Q)=0\quad\text{for every }f\in A_{n-1}^{(n)}.
--   $$
--
--   A low-rank frequency cannot correlate with the determinant, which makes $\det$ the hard target for the method.
--
--   Differences from the source:
--
--   - encoding: $n$ a dimension → hypothesis `1 ≤ n`; reason: at $n=0$ the index $n-1$ is undefined
--   - encoding: orthogonality of $\det$ to $V_{n-1}^{(n)}$ → $\int\det\cdot f\,d\mu_n=0$ for $f\in V_{n-1}^{(n)}$; reason: $\det$ is real, so this is the $L^2$ inner product
-- source:
--   Augustino et al., Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank, arXiv:2609.09035, Lemma 3.4, p.19

import Mathlib
import Definitions.Def_FourierRankQLB_Vr
import Definitions.Def_FourierRankQLB_Ar

open MeasureTheory

namespace FourierRankQLB

/-- Lemma 3.4 (Reflection orthogonality). If `rank Ξ < n` then `∫ det(Q) χ_Ξ(Q) dμ_n = 0` (23).
Consequently `Q ↦ det Q` is orthogonal to `V_{n-1}^{(n)}`, and `∫ det(Q) f(Q) dμ_n = 0` for every
`f ∈ A_{n-1}^{(n)}` (24).

Augustino et al., *Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank*, arXiv:2609.09035, Lemma 3.4, p. 19.

**Formalization Note.** `n ≥ 1`, since `O(0)` has no reflection and `n - 1` is truncated there. The
function `det` is real, so its `L²` inner product with `f` is the integral of `det · f`. -/
theorem lemma_3_4 {n : ℕ} (hn : 1 ≤ n) :
    (∀ Ξ : Matrix (Fin n) (Fin n) ℝ, Ξ.rank < n →
      ∫ Q : Od n, (((Q : Matrix (Fin n) (Fin n) ℝ).det : ℝ) : ℂ) * chi Ξ Q ∂haarO n = 0) ∧
    (∀ f ∈ Vr n (n - 1),
      ∫ Q : Od n, (((Q : Matrix (Fin n) (Fin n) ℝ).det : ℝ) : ℂ) * f Q ∂haarO n = 0) ∧
    (∀ f ∈ Ar n (n - 1),
      ∫ Q : Od n, (((Q : Matrix (Fin n) (Fin n) ℝ).det : ℝ) : ℂ) * f Q ∂haarO n = 0) := by sorry

end FourierRankQLB
