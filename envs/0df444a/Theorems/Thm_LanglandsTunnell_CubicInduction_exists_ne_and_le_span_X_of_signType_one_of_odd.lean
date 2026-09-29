-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_ne_and_le_span_X_of_signType_one_of_odd
-- name    : LanglandsTunnell.CubicInduction.exists_ne_and_le_span_X_of_signType_one_of_odd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/18a8e6c1-4d4c-5808-9e0f-f7e2ac142aa2
-- title:
--   Degree-one odd sign classes lie in a coordinate line
-- statement:
--   Let $b_0,c_0\in\{0,1,2\}$ be non-zero and distinct, so that $\{0,b_0,c_0\}$ exhausts $\{0,1,2\}$, and let $\varepsilon\colon\{0,1,2\}\to\mathbb Z/2$ (realised as `Fin 3 → Fin 2`) satisfy $\varepsilon_0\neq\varepsilon_{b_0}$ (the "odd" condition). Let $S$ be a family of $\mathbb C$-submodules $S(\ell)$ of $\mathbb C[x_0,x_1,x_2]=$ `MvPolynomial (Fin 3) ℂ`, indexed by $\ell\in\mathbb N$, subject to two hypotheses: first, every $p\in S(\ell)$ is homogeneous of degree $\ell$ and harmonic, i.e. $\sum_{i}\partial_i^2 p=0$; second, every $p\in S(\ell)$ is an eigenvector for all sign changes of the variables, in the sense that for every $\sigma\colon\{0,1,2\}\to\mathbb Z/2$ the substitution $x_a\mapsto(-1)^{\sigma_a}x_a$ multiplies $p$ by $(-1)^{\sum_a(\varepsilon_a+\ell+\sum_b\varepsilon_b)\sigma_a}$, the exponents being read as natural numbers via the representatives $0,1$. The conclusion asserts the existence of an index $m\neq c_0$ such that $S(1)$ is contained in the line $\mathbb C\,x_m$ spanned by the single variable $x_m$, together with the parity identity $(1+\sum_a\varepsilon_a)\bmod 2=\varepsilon_{c_0}$.
--
--   This is the sign bookkeeping needed for the odd sign classes in the cubic induction: a linear form of pure sign type $\chi_\varepsilon\cdot\det^{\,1+\sum\varepsilon}$ must be a multiple of a single coordinate $x_m$ with $m\neq c_0$, and the determinant exponent has parity $\varepsilon_{c_0}$. It is used to read off the bottom vector of an odd isotypic piece and feeds into the two statements citing it in the same development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_ne_and_le_span_X_of_signType_one_of_odd.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem LanglandsTunnell.CubicInduction.exists_ne_and_le_span_X_of_signType_one_of_odd
    (b₀ c₀ : Fin 3) (hb₀ : b₀ ≠ 0) (hc₀ : c₀ ≠ 0) (hbc : b₀ ≠ c₀)
    (ε : Fin 3 → Fin 2) (hodd : ε 0 ≠ ε b₀)
    (S : ℕ → Submodule ℂ (MvPolynomial (Fin 3) ℂ))
    (hS : (∀ ℓ, ∀ p : MvPolynomial (Fin 3) ℂ, p ∈ S ℓ →
            p.IsHomogeneous ℓ ∧ (∑ i : Fin 3, MvPolynomial.pderiv i (MvPolynomial.pderiv i p)) = 0))
    (hsign : (∀ ℓ, ∀ p ∈ S ℓ, ∀ σ : Fin 3 → Fin 2,
        MvPolynomial.aeval (fun a : Fin 3 => MvPolynomial.C ((-1 : ℂ) ^ (σ a : ℕ)) * MvPolynomial.X a) p =
          MvPolynomial.C ((-1 : ℂ) ^ (∑ a : Fin 3, ((ε a : ℕ) + ℓ + ∑ b : Fin 3, (ε b : ℕ)) * (σ a : ℕ))) * p)) :
    ∃ m : Fin 3, m ≠ c₀ ∧ S 1 ≤ Submodule.span ℂ {(MvPolynomial.X m : MvPolynomial (Fin 3) ℂ)} ∧
      (1 + ∑ a : Fin 3, (ε a : ℕ)) % 2 = (ε c₀ : ℕ) := by sorry
