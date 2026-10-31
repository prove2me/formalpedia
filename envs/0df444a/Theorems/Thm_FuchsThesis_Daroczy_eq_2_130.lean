-- Prove2me | Theorems.Thm_FuchsThesis_Daroczy_eq_2_130
-- name    : FuchsThesis.Daroczy.eq_2_130
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:22:37.620723+00:00
-- url     : https://prove2.me/theorems/37cf983c-20bc-4da7-bf51-762ed3dfc115
-- title:
--   Eq. (2.130): $H_\alpha(p)=C(2^{1-\alpha}-1)^{-1}(\sum_i p_i^\alpha-1)$
-- statement:
--   Let $\alpha > 0$ with $\alpha \ne 1$, and let $H_\alpha : \Gamma \to \mathbb R$ be symmetric and satisfy the recursion (2.111) of type $\alpha$. Then for every $n$ and every $(p_1,\dots,p_n) \in \Gamma_n$,
--
--   $$
--   H_\alpha(p_1,\dots,p_n) = C\,\big(2^{1-\alpha} - 1\big)^{-1} \left( \sum_{i=1}^{n} p_i^{\alpha} - 1 \right), \qquad C = H_\alpha\!\left(\tfrac12, \tfrac12\right).
--   $$
--
--   Every symmetric solution of the recursion of type $\alpha$ is therefore a constant multiple of the Daróczy information of type $\alpha$. This is the closed form whose limit $\alpha \to 1$ gives the Shannon entropy (Theorem 2.7).
--
--   **Formalization Note** Powers are real powers, so a zero entry contributes $0^\alpha = 0$. For $n = 1$ both sides are $0$.
--
--   Differences from the source:
--   - encoding: recursion (2.111) for every $n \ge 2$ → recursion required only when $p_1 + p_2 > 0$; reason: the right side of (2.111) is undefined at $p_1 + p_2 = 0$, so this only excludes undefined cases
-- source:
--   Fuchs, Distinguishability and Accessible Information in Quantum Theory, arXiv:quant-ph/9601020v1, eq. (2.130), p.34 (PDF p.43)

import Mathlib
import Definitions.Def_FuchsThesis_Daroczy_IsDist
import Definitions.Def_FuchsThesis_Daroczy_IsSymmetric
import Definitions.Def_FuchsThesis_Daroczy_SatisfiesRecursion

namespace FuchsThesis.Daroczy

/-- Fuchs, *Distinguishability and Accessible Information in Quantum Theory*,
arXiv:quant-ph/9601020v1, eq. (2.130), p.34 (PDF p.43), in the proof of Theorem 2.7: every
symmetric `H_α` satisfying (2.111) is a multiple of the Daróczy information of type `α`:
`H_α(p₁, …, pₙ) = C (2^{1−α} − 1)^{−1} (∑_{i=1}^{n} p_i^α − 1)` for every `n` and every
`(p₁, …, pₙ) ∈ Γₙ`, with `C = f(1/2) = H_α(1/2, 1/2)`.

**Formalization Note.** Stated for every `n`; `Γ₀` is empty, and at `n = 1` both sides are `0`
(`H_α(1) = 0` follows from (2.111) at `(1, 0)`). Powers are `Real.rpow`, so a zero entry
contributes `0 ^ α = 0` for `α > 0`. `α > 0, α ≠ 1` is the standing assumption of §2.4.1. -/
theorem eq_2_130 (α : ℝ) (hα : 0 < α) (hα1 : α ≠ 1) (H : (n : ℕ) → (Fin n → ℝ) → ℝ)
    (hsym : IsSymmetric H) (hrec : SatisfiesRecursion α H)
    (n : ℕ) (p : Fin n → ℝ) (hp : IsDist p) :
    H n p = H 2 ![1 / 2, 1 - 1 / 2] * ((2 : ℝ) ^ (1 - α) - 1)⁻¹ *
      (∑ i, p i ^ α - 1) := by sorry

end FuchsThesis.Daroczy
