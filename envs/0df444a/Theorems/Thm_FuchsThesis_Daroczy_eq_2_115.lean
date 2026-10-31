-- Prove2me | Theorems.Thm_FuchsThesis_Daroczy_eq_2_115
-- name    : FuchsThesis.Daroczy.eq_2_115
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:22:20.081153+00:00
-- url     : https://prove2.me/theorems/9ceb3625-ccc3-4bc5-a023-5e3fa2047cea
-- title:
--   Eq. (2.115): $H_\alpha(p)=\sum_{i=2}^n s_i^\alpha f(p_i/s_i)$
-- statement:
--   Let $\alpha > 0$ with $\alpha \ne 1$, and let $H_\alpha : \Gamma \to \mathbb R$ be symmetric and satisfy the recursion (2.111) of type $\alpha$. Write $f(x) = H_\alpha(x, 1-x)$ for $0 \le x \le 1$ (Eq. (2.114)). For a distribution $(p_1,\dots,p_n) \in \Gamma_n$ let $s_i = p_1 + \dots + p_i$ be its partial sums. Then
--
--   $$
--   H_\alpha(p_1,\dots,p_n) = \sum_{i=2}^{n} s_i^{\alpha}\, f\!\left(\frac{p_i}{s_i}\right).
--   $$
--
--   This reduces the determination of $H_\alpha$ on every $\Gamma_n$ to the determination of the single function $f$ of one variable.
--
--   **Formalization Note** Indices are 0-based in Lean. A term with $s_i = 0$ (all of $p_1,\dots,p_i$ zero) is undefined in the source; Lean evaluates it as $0^\alpha f(0) = 0$ because $\alpha > 0$.
--
--   Differences from the source:
--   - encoding: recursion (2.111) for every $n \ge 2$ → recursion required only when $p_1 + p_2 > 0$; reason: the right side of (2.111) is undefined at $p_1 + p_2 = 0$, so this only excludes undefined cases
--   - encoding: terms with $s_i = 0$ undefined in (2.115) → such a term is $0^\alpha f(0/0) = 0$ in Lean; reason: the factor $s_i^\alpha$ is $0$ for $\alpha > 0$, so the term contributes nothing whatever value $f$ takes
-- source:
--   Fuchs, Distinguishability and Accessible Information in Quantum Theory, arXiv:quant-ph/9601020v1, eq. (2.115) with (2.114), p.32 (PDF p.41)

import Mathlib
import Definitions.Def_FuchsThesis_Daroczy_IsDist
import Definitions.Def_FuchsThesis_Daroczy_IsSymmetric
import Definitions.Def_FuchsThesis_Daroczy_SatisfiesRecursion

namespace FuchsThesis.Daroczy

/-- Fuchs, *Distinguishability and Accessible Information in Quantum Theory*,
arXiv:quant-ph/9601020v1, eq. (2.115), p.32 (PDF p.41), in the proof of Theorem 2.7: for a
symmetric `H_α` satisfying (2.111), with `s_i = p₁ + ⋯ + p_i` and `f(x) = H_α(x, 1 − x)`
(2.114),
`H_α(p₁, …, pₙ) = ∑_{i=2}^{n} s_i^α f(p_i / s_i)` for every `(p₁, …, pₙ) ∈ Γₙ`.

**Formalization Note.** Indices are 0-based: the source's `i = 2, …, n` is `i : Fin n` with
`1 ≤ i`, and `s_i` is `∑_{j ≤ i} p j`. A term with `s_i = 0` (all of `p₁, …, p_i` zero) is
undefined in the source; in Lean it is `0 ^ α * f(0 / 0) = 0` since `α > 0`, whatever `f(0)` is.
`α > 0, α ≠ 1` is the standing assumption of §2.4.1 ("an arbitrary positive parameter α ≠ 1"). -/
theorem eq_2_115 (α : ℝ) (hα : 0 < α) (hα1 : α ≠ 1) (H : (n : ℕ) → (Fin n → ℝ) → ℝ)
    (hsym : IsSymmetric H) (hrec : SatisfiesRecursion α H)
    (n : ℕ) (p : Fin n → ℝ) (hp : IsDist p) :
    H n p = ∑ i ∈ Finset.univ.filter (fun i : Fin n => 1 ≤ (i : ℕ)),
      (∑ j ∈ Finset.Iic i, p j) ^ α *
        H 2 ![p i / ∑ j ∈ Finset.Iic i, p j, 1 - p i / ∑ j ∈ Finset.Iic i, p j] := by sorry

end FuchsThesis.Daroczy
