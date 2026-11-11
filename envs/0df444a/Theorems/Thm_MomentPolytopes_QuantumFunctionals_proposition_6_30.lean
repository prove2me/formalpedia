-- Prove2me | Theorems.Thm_MomentPolytopes_QuantumFunctionals_proposition_6_30
-- name    : MomentPolytopes.QuantumFunctionals.proposition_6_30
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T01:05:29.250797+00:00
-- url     : https://prove2.me/theorems/fa05fa7c-4a23-4136-9fb7-92196b14ede5
-- title:
--   Proposition 6.30 — for Gaussian-integer T and p ∈ A, log cap_p(T) > −∞ ⇔ log cap_p(T) ≥ −Σ_ℓ log n_ℓ
-- statement:
--   Let $0\ne T\in\mathrm{Ten}(n_0;n_1,\dots,n_d)$ have Gaussian integer entries. Then for every $p\in A=\operatorname{diag}(\mathbb R^{n_1})\times\dots\times\operatorname{diag}(\mathbb R^{n_d})$,
--   $$\log\operatorname{cap}_p(T)>-\infty\iff\log\operatorname{cap}_p(T)\ \ge\ -\sum_{\ell=1}^d\log n_\ell .$$
--
--   The paper cites this capacity lower bound from [BFG+18, Thm. 2.13] (with the extension to Gaussian integers and all of $A$ explained in its fn. 32); it is a step of the proof of Theorem 6.28.
--
--   Differences from the source:
--   - encoding: ℓ ∈ [d] = {1, …, d} → ℓ : Fin d (0-based); reason: indexing convention; same instances
--   - encoding: log Cap and log cap in [−∞, ∞) → EReal, −∞ = ⊥; the bound is an EReal inequality; reason: Lean convention; same values, no junk value for −∞
--   - generalization: Ten(n_0; n_1, …, n_d) with d ≥ 1 → any d : ℕ, including d = 0; reason: d = 0 is a degenerate case (trivial group, Δ(T) a point) where the claim holds; at d ≥ 1 the statement is the source's
--   - encoding: p ∈ A = diag(ℝ^{n_1}) × ⋯ × diag(ℝ^{n_d}) → p : SpecTuple n (any real vectors), read as diagTuple p; reason: the identification A ≅ ℝ^{n_1} × ⋯ × ℝ^{n_d} of Example 2.1
-- source:
--   Doğan, Sakabe, Walter, Convex optimization on moment polytopes, arXiv:2609.06633 (PDF sha256 fcf40771…), p. 45, Proposition 6.30 (cited from [BFG+18, Thm. 2.13])

import Mathlib
import Definitions.Def_MomentPolytopes_QuantumFunctionals_TensorAction
import Definitions.Def_MomentPolytopes_QuantumFunctionals_EntanglementPolytope
import Definitions.Def_MomentPolytopes_QuantumFunctionals_Capacity
import Definitions.Def_MomentPolytopes_QuantumFunctionals_GaussianInteger

set_option autoImplicit false

open scoped ComplexOrder Matrix

namespace MomentPolytopes.QuantumFunctionals

/-- Proposition 6.30 (p. 45, cited from [BFG+18, Thm. 2.13]). For a nonzero tensor tuple with
Gaussian integer entries and every `p ∈ A` (every tuple of real diagonal matrices),
`log cap_p(T) > −∞ ⟺ log cap_p(T) ≥ −∑_ℓ log n_ℓ`. -/
theorem proposition_6_30 {d n0 : ℕ} {n : Fin d → ℕ} (T : Ten d n0 n) (hT : T ≠ 0)
    (hGauss : IsGaussianInteger T) (p : SpecTuple n) :
    ⊥ < logCapX (diagTuple p) T ↔
      ((-∑ ℓ, Real.log (n ℓ) : ℝ) : EReal) ≤ logCapX (diagTuple p) T := by sorry

end MomentPolytopes.QuantumFunctionals
