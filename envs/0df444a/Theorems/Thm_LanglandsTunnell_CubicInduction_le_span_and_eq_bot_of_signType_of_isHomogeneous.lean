-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_le_span_and_eq_bot_of_signType_of_isHomogeneous
-- name    : LanglandsTunnell.CubicInduction.le_span_and_eq_bot_of_signType_of_isHomogeneous
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/f2b584d5-1ee4-5daa-a96a-1e19b9d4341e
-- title:
--   Low-degree members of harmonic families with pure sign type
-- statement:
--   Let $\varepsilon : \mathrm{Fin}\,3 \to \mathrm{Fin}\,2$ be a triple of signs and let $S$ assign to each natural number $\ell$ a $\mathbb{C}$-submodule $S\,\ell$ of $\mathbb{C}[x_0,x_1,x_2]$. Assume two hypotheses on $S$: first, every $p \in S\,\ell$ is homogeneous of degree $\ell$ and satisfies $\sum_{i} \partial_i \partial_i p = 0$; second, every $p \in S\,\ell$ has pure sign type in the sense that for all $\sigma : \mathrm{Fin}\,3 \to \mathrm{Fin}\,2$ the substitution $x_a \mapsto (-1)^{\sigma_a} x_a$ sends $p$ to $(-1)^{\sum_a (\varepsilon_a + \ell + \sum_b \varepsilon_b)\sigma_a}\,p$, the exponents being the values of $\varepsilon_a, \sigma_a \in \{0,1\}$. Let $b_0, c_0 \in \mathrm{Fin}\,3$ with $b_0 \neq 0$, $c_0 \neq 0$ and $b_0 \neq c_0$, so that $\{0, b_0, c_0\} = \mathrm{Fin}\,3$. The conclusion is a conjunction of two implications. If $\varepsilon_0 = \varepsilon_{b_0}$ and $\varepsilon_0 = \varepsilon_{c_0}$, then $S\,0 \le \mathbb{C}\cdot 1$, $S\,1 = 0$, and $S\,2$ lies in the span of $x_0^2 - x_2^2$ and $x_1^2 - x_2^2$. If instead $\varepsilon_0 = \varepsilon_{b_0}$ and $\varepsilon_0 \neq \varepsilon_{c_0}$, then $S\,0 = 0$, $S\,1$ lies in the span of $x_{c_0}$, and $S\,2$ lies in the span of $x_0 x_{b_0}$.
--
--   This is the sign-counting step that pins down the members of degree at most $2$ in a family of harmonic homogeneous polynomials in three variables transforming by a single character of the group of sign changes, the two cases corresponding to $\varepsilon$ constant and to $\varepsilon$ taking both values. It supplies the containment clauses used in the construction of transition-stable families in the cubic induction underlying the Langlands–Tunnell argument, and is cited by [`LanglandsTunnell.CubicInduction.exists_transitionStable_families_ne_bot_of_inducedPicture_package_top`](thm.html#LanglandsTunnell.CubicInduction.exists_transitionStable_families_ne_bot_of_inducedPicture_package_top).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_le_span_and_eq_bot_of_signType_of_isHomogeneous.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem LanglandsTunnell.CubicInduction.le_span_and_eq_bot_of_signType_of_isHomogeneous
    (ε : Fin 3 → Fin 2) (S : ℕ → Submodule ℂ (MvPolynomial (Fin 3) ℂ))
    (hS : (∀ ℓ, ∀ p : MvPolynomial (Fin 3) ℂ, p ∈ S ℓ →
            p.IsHomogeneous ℓ ∧ (∑ i : Fin 3, MvPolynomial.pderiv i (MvPolynomial.pderiv i p)) = 0))
    (hsign : (∀ ℓ, ∀ p ∈ S ℓ, ∀ σ : Fin 3 → Fin 2,
        MvPolynomial.aeval (fun a : Fin 3 => MvPolynomial.C ((-1 : ℂ) ^ (σ a : ℕ)) * MvPolynomial.X a) p =
          MvPolynomial.C ((-1 : ℂ) ^ (∑ a : Fin 3, ((ε a : ℕ) + ℓ + ∑ b : Fin 3, (ε b : ℕ)) * (σ a : ℕ))) * p))
    (b₀ c₀ : Fin 3) (hb₀ : b₀ ≠ 0) (hc₀ : c₀ ≠ 0) (hbc : b₀ ≠ c₀) :
    ((ε 0 = ε b₀ ∧ ε 0 = ε c₀) →
      S 0 ≤ Submodule.span ℂ {(1 : MvPolynomial (Fin 3) ℂ)} ∧
          S 1 = ⊥ ∧
          S 2 ≤ Submodule.span ℂ {MvPolynomial.X 0 ^ 2 - MvPolynomial.X 2 ^ 2,
            MvPolynomial.X 1 ^ 2 - MvPolynomial.X 2 ^ 2}) ∧
    ((ε 0 = ε b₀ ∧ ε 0 ≠ ε c₀) →
      S 0 = ⊥ ∧
          S 1 ≤ Submodule.span ℂ {(MvPolynomial.X c₀ : MvPolynomial (Fin 3) ℂ)} ∧
          S 2 ≤ Submodule.span ℂ {(MvPolynomial.X 0 * MvPolynomial.X b₀ : MvPolynomial (Fin 3) ℂ)}) := by sorry
