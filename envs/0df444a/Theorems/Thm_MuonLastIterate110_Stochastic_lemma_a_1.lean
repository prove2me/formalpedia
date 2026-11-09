-- Prove2me | Theorems.Thm_MuonLastIterate110_Stochastic_lemma_a_1
-- name    : MuonLastIterate110.Stochastic.lemma_a_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:05:53.058393+00:00
-- url     : https://prove2.me/theorems/174a2111-f780-45da-987a-344b7f5d81a4
-- title:
--   Lemma A.1 — gradient self-bound
-- statement:
--   Let $F:\mathbb R^{m\times n}\to\mathbb R$ satisfy Assumption 3.1: $F$ is continuously differentiable, $F\ge F_{\inf}$, and $\nabla F$ is $L$-Lipschitz with $L>0$. Then for every $X\in\mathbb R^{m\times n}$,
--
--   $$
--   \|\nabla F(X)\|^2\le2L\bigl(F(X)-F_{\inf}\bigr).
--   $$
--
--   No convexity and no attained minimizer are assumed. The bound turns control of the objective gap into control of the gradient; the paper uses it to dominate $\|g_t\|^2$ uniformly along a trajectory.
--
--   Differences from the source:
--
--   - encoding: real m×n matrices with Frobenius norm ‖X‖_F and inner product tr(XᵀY) → EuclideanSpace ℝ (Fin m × Fin n), read as a matrix through toMat for the products of (3.4); reason: the Euclidean norm and inner product on this type are exactly the Frobenius ones (checked in the sanity file); same instances
-- source:
--   Ping Li and Vincent Y. F. Tan, Last-Iterate Stationarity of Muon with Finitely Many Newton-Schulz Iterations, STOC 2027 submission #110 preprint (2026), source.pdf SHA-256 5362e7185a9ddcba39d1a70da110a8b04f1d179ad818e6d5d0ec73bf29586372, p.14, Lemma A.1, (A.3); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/110.pdf

import Mathlib
import Definitions.Def_MuonLastIterate110_Stochastic_Muon

namespace MuonLastIterate110.Stochastic

/-- Lemma A.1 (Gradient self-bound), p.14, (A.3): under Assumption 3.1,
`‖∇F(X)‖² ≤ 2L (F(X) − F_inf)` for every `X ∈ ℝ^{m×n}`. -/
theorem lemma_a_1 {m n : ℕ} (F : Mat m n → ℝ) (L Finf : ℝ) (hF : Assumption31 F L Finf)
    (X : Mat m n) :
    ‖gradient F X‖ ^ 2 ≤ 2 * L * (F X - Finf) := by sorry

end MuonLastIterate110.Stochastic
