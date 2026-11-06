-- Prove2me | Theorems.Thm_NondualOpt_lemma_19
-- name    : NondualOpt.lemma_19
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T23:58:44.581579+00:00
-- url     : https://prove2.me/theorems/9598ded7-c46d-41f9-ac50-abc5c6a1ab87
-- title:
--   Lemma 19 — finite-class offset estimate
-- statement:
--   Let $b>0$, $T\ge1$, and let $A$ be a finite nonempty family of pair-trees $a=\{a^+_t(\varepsilon_{1:t-1}),a^-_t(\varepsilon_{1:t-1})\}_{t\le T}$ with values in $[0,b]$. For
--   $$
--   M_a(\varepsilon)=\sum_{t=1}^T\Big(a^{-\varepsilon_t}_t(\varepsilon_{1:t-1})-2a^{\varepsilon_t}_t(\varepsilon_{1:t-1})\Big)
--   $$
--   and independent uniform signs $\varepsilon\in\{\pm1\}^T$,
--   $$
--   \mathbb E_\varepsilon\Big[\sup_{a\in A}\frac1TM_a(\varepsilon)\Big]_+\le\frac{4b}T\big(1+\log|A|\big).
--   $$
--   The offset factor $2$ makes each summand's exponential moment at most one, so a finite class costs only $\log|A|$; this is the base step of the chaining in Proposition 20.
--
--   Differences from the source:
--   - encoding: signs ε_t ∈ {±1}, pair-trees (a⁺, a⁻), E_ε → Bool signs (true ↦ +1), trees with values in ℝ × ℝ, the uniform average over {±1}^T with the positive part inside; reason: same instances; the proof integrates the tail of the supremum
--   - encoding: rounds t ≤ T → T ≥ 1, rounds Fin T; reason: the bound divides by T
-- source:
--   Bullins–Guzmán–Martínez-Rubio–Molina, The First-Order Oracle Complexity of Lipschitz Convex Optimization in Nondual Settings, arXiv:2609.20687, Lemma 19, (15), p.27

import Mathlib
import Definitions.Def_NondualOpt_Tree
import Definitions.Def_NondualOpt_histPrefix

namespace NondualOpt

/-- **Lemma 19 (Finite-class offset estimate).** Let `b > 0` and `A` a finite nonempty family of
pair-trees `a = {a⁺_t(ε_{1:t−1}), a⁻_t(ε_{1:t−1})}_{t ≤ T}` with values in `[0, b]`. For
`M_a(ε) = ∑_t (a^{−ε_t}_t(ε_{1:t−1}) − 2 a^{ε_t}_t(ε_{1:t−1}))`,
`E_ε [sup_{a ∈ A} (1/T) M_a(ε)]₊ ≤ (4b/T)(1 + log |A|)`.
Bullins–Guzmán–Martínez-Rubio–Molina, arXiv:2609.20687, Lemma 19, (15), p.27.

**Formalization Note.** A pair-tree is a tree with values `(a⁺, a⁻) ∈ ℝ × ℝ`; signs are `Bool`
(`true ↦ +1`), so for `ε_t = +1` the summand is `a⁻ − 2a⁺`. `E_ε` is the uniform average over
`{±1}^T`, and the positive part is taken inside the expectation, as in the proof. `T ≥ 1`. -/
theorem lemma_19 (T : ℕ) (hT : 1 ≤ T) (b : ℝ) (hb : 0 < b) (A : Finset (Tree (ℝ × ℝ) T))
    (hA : A.Nonempty)
    (hval : ∀ a ∈ A, ∀ t ε, 0 ≤ (a t ε).1 ∧ (a t ε).1 ≤ b ∧ 0 ≤ (a t ε).2 ∧ (a t ε).2 ≤ b) :
    (1 / 2 ^ T : ℝ) * ∑ ε : Fin T → Bool,
        max (A.sup' hA (fun a => (1 / T : ℝ) * ∑ t,
          (if ε t then (a t (histPrefix ε t)).2 - 2 * (a t (histPrefix ε t)).1
            else (a t (histPrefix ε t)).1 - 2 * (a t (histPrefix ε t)).2))) 0 ≤
      4 * b / T * (1 + Real.log A.card) := by sorry

end NondualOpt
