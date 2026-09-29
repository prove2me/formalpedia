-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_mem_eval_eq_det_pow_mul_entry_of_odd_signClass_of_actStable
-- name    : LanglandsTunnell.CubicInduction.exists_mem_eval_eq_det_pow_mul_entry_of_odd_signClass_of_actStable
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/216998c7-2510-577f-85e5-0c809d756966
-- title:
--   Odd sign class forces a det-twisted row entry
-- statement:
--   Fix real numbers $\sigma,\sigma_3$ and indices $b_0,c_0\in\{0,1,2\}$ with $b_0\neq 0$, $c_0\neq 0$, $b_0\neq c_0$ (so $\{0,b_0,c_0\}$ exhausts `Fin 3`), let $\nu:\mathrm{Fin}\,3\to\mathbb{C}$ satisfy $\nu_0=-1/2+i\sigma$, $\nu_{b_0}=1/2+i\sigma$, $\nu_{c_0}=i\sigma_3$, and let $\varepsilon:\mathrm{Fin}\,3\to\mathbb{Z}/2$ satisfy $\varepsilon_0\neq\varepsilon_{b_0}$. Let $W$ be a $\mathbb{C}$-submodule of the polynomial ring in the nine variables $X_{a,c}$, $(a,c)\in\mathrm{Fin}\,3\times\mathrm{Fin}\,3$. Write $\mathrm{act}\,\nu\,c\,d$ for the operator $p\mapsto\bigl(\sum_a(\nu_a+e_a)X_{a,c}X_{a,d}\bigr)p+\sum_{i,j}\bigl(\sum_m s_{i,m}(c,d)X_{m,j}\bigr)\partial_{(i,j)}p$, where $e=(1,0,-1)$ and $s_{i,m}(c,d)$ is $X_{i,c}X_{m,d}$ for $m<i$, $-X_{m,c}X_{i,d}$ for $i<m$, and $0$ for $m=i$. Assume: (i) $W$ is stable under every $\mathrm{act}\,\nu\,c\,d$; (ii) $W$ is stable under the substitutions $X_{i,j}\mapsto\sum_c X_{i,c}r_{c,j}$ for every real matrix $r$ with $\sum_a r_{a,i}r_{a,j}=\delta_{ij}$; (iii) for every $P\in W$, every $\tau:\mathrm{Fin}\,3\to\mathbb{Z}/2$ and every real $o$ with $\sum_a o_{a,i}o_{a,j}=\delta_{ij}$, the value of $P$ at $\mathrm{diag}((-1)^{\tau_a})\,o$ equals $(-1)^{\sum_a\varepsilon_a\tau_a}$ times its value at $o$; (iv) some $P\in W$ is non-zero at some such $o$. Then there exist $m\neq c_0$, an index $j$ and $Q\in W$ with $Q(o)=\det(o)^{\varepsilon_{c_0}}\,o_{m,j}$ for every real $o$ with $\sum_a o_{a,i}o_{a,j}=\delta_{ij}$.
--
--   This is the step, in the Langlands–Tunnell part of the argument, which says that a $(\mathfrak{g},K)$-stable space of polynomial functions on $O(3)$ lying in an odd sign class $\chi_\varepsilon$ and not identically zero on $O(3)$ reaches the lowest $O(3)$-type of the corresponding principal series, namely the three-dimensional space spanned by $\det^{\varepsilon_{c_0}}\!\cdot o_{mj}$. It is used in [`LanglandsTunnell.CubicInduction.forall_eval_orthogonal_eq_zero_of_odd_signClass_of_positive_actSkew_form`](thm.html#LanglandsTunnell.CubicInduction.forall_eval_orthogonal_eq_zero_of_odd_signClass_of_positive_actSkew_form).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_mem_eval_eq_det_pow_mul_entry_of_odd_signClass_of_actStable.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem LanglandsTunnell.CubicInduction.exists_mem_eval_eq_det_pow_mul_entry_of_odd_signClass_of_actStable
    (σ σ₃ : ℝ) (b₀ c₀ : Fin 3) (hb₀ : b₀ ≠ 0) (hc₀ : c₀ ≠ 0) (hbc : b₀ ≠ c₀)
    (ν : Fin 3 → ℂ) (hν0 : ν 0 = -1 / 2 + σ * Complex.I) (hνb : ν b₀ = 1 / 2 + σ * Complex.I)
    (hνc : ν c₀ = σ₃ * Complex.I)
    (ε : Fin 3 → Fin 2) (hodd : ε 0 ≠ ε b₀)
    (W : Submodule ℂ (MvPolynomial (Fin 3 × Fin 3) ℂ)) :
    let act : (Fin 3 → ℂ) → Fin 3 → Fin 3 →
        MvPolynomial (Fin 3 × Fin 3) ℂ → MvPolynomial (Fin 3 × Fin 3) ℂ :=
      fun ν c d p =>
        (∑ a : Fin 3, MvPolynomial.C (ν a + (![1, 0, -1] : Fin 3 → ℂ) a) *
            (MvPolynomial.X (a, c) * MvPolynomial.X (a, d))) * p +
        ∑ i : Fin 3, ∑ j : Fin 3,
          (∑ m : Fin 3,
            (if m < i then MvPolynomial.X (i, c) * MvPolynomial.X (m, d)
              else if i < m then -(MvPolynomial.X (m, c) * MvPolynomial.X (i, d))
              else (0 : MvPolynomial (Fin 3 × Fin 3) ℂ)) * MvPolynomial.X (m, j)) *
            MvPolynomial.pderiv (i, j) p
    (∀ P ∈ W, ∀ c d : Fin 3, act ν c d P ∈ W) →
    (∀ P ∈ W, ∀ r : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, ∑ a : Fin 3, r a i * r a j = if i = j then 1 else 0) →
        MvPolynomial.aeval (fun ij : Fin 3 × Fin 3 =>
            ∑ c : Fin 3, MvPolynomial.X (ij.1, c) * MvPolynomial.C ((r c ij.2 : ℝ) : ℂ)) P ∈ W) →
    (∀ P ∈ W, ∀ τ : Fin 3 → Fin 2, ∀ o : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) →
        MvPolynomial.eval (fun ij : Fin 3 × Fin 3 => (((∑ c : Fin 3, (fun a b => if a = b then (-1 : ℝ) ^ (τ a : ℕ) else 0) ij.1 c * o c ij.2) : ℝ) : ℂ)) P =
          (-1 : ℂ) ^ (∑ a : Fin 3, (ε a : ℕ) * (τ a : ℕ)) * MvPolynomial.eval (fun ij : Fin 3 × Fin 3 => ((o ij.1 ij.2 : ℝ) : ℂ)) P) →
    (∃ P ∈ W, ∃ o : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) ∧ MvPolynomial.eval (fun ij : Fin 3 × Fin 3 => ((o ij.1 ij.2 : ℝ) : ℂ)) P ≠ 0) →
    ∃ m : Fin 3, m ≠ c₀ ∧ ∃ j : Fin 3, ∃ Q ∈ W, ∀ o : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) →
      MvPolynomial.eval (fun ij : Fin 3 × Fin 3 => ((o ij.1 ij.2 : ℝ) : ℂ)) Q = (Matrix.of fun i j : Fin 3 => ((o i j : ℝ) : ℂ)).det ^ (ε c₀ : ℕ) * ((o m j : ℝ) : ℂ) := by sorry
