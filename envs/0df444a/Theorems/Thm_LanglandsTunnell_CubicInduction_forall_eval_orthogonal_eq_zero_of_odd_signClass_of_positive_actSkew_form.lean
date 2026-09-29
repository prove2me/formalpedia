-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_forall_eval_orthogonal_eq_zero_of_odd_signClass_of_positive_actSkew_form
-- name    : LanglandsTunnell.CubicInduction.forall_eval_orthogonal_eq_zero_of_odd_signClass_of_positive_actSkew_form
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/04b10398-f4d9-51f0-9970-7450fa2cdee7
-- title:
--   No positive invariant form on an odd sign class
-- statement:
--   Fix reals $\sigma,\sigma_3$, indices $b_0,c_0\in\{0,1,2\}$ with $b_0\neq 0$, $c_0\neq 0$, $b_0\neq c_0$, and $\nu:\{0,1,2\}\to\mathbb{C}$ with $\nu_0=-\tfrac12+\sigma i$, $\nu_{b_0}=\tfrac12+\sigma i$, $\nu_{c_0}=\sigma_3 i$; fix $\varepsilon:\{0,1,2\}\to\mathbb{Z}/2$ with $\varepsilon_0\neq\varepsilon_{b_0}$, a $\mathbb{C}$-submodule $W$ of the polynomial ring in the nine variables $X_{a,c}$, and a function $\beta$ of two such polynomials with values in $\mathbb{C}$. Write $\mathrm{act}\,\nu\,c\,d\,p=\bigl(\sum_a (\nu_a+v_a)X_{a,c}X_{a,d}\bigr)p+\sum_{i,j}\bigl(\sum_m \epsilon_{i,m}\,X_{m,j}\bigr)\,\partial p/\partial X_{i,j}$, where $v=(1,0,-1)$ and $\epsilon_{i,m}$ is $X_{i,c}X_{m,d}$ for $m<i$, $-X_{m,c}X_{i,d}$ for $i<m$, and $0$ for $m=i$. Call a real $3\times3$ matrix $o$ orthogonal when $\sum_a o_{a i}o_{a j}=\delta_{ij}$. Assume: $W$ is stable under every $\mathrm{act}\,\nu\,c\,d$ and under the substitutions $X_{i,j}\mapsto\sum_c X_{i,c}\,r_{c,j}$ for orthogonal $r$; each $P\in W$ satisfies $P(\mathrm{diag}((-1)^{\tau_a})\,o)=(-1)^{\sum_a\varepsilon_a\tau_a}P(o)$ for all $\tau:\{0,1,2\}\to\mathbb{Z}/2$ and orthogonal $o$; $\beta$ is linear in its first argument on $W$, Hermitian ($\beta(Q,P)=\overline{\beta(P,Q)}$), annihilates in its first argument any $P\in W$ vanishing at all orthogonal matrices, satisfies $\operatorname{Re}\beta(P,P)>0$ whenever $P\in W$ is non-zero at some orthogonal matrix, is invariant under the above orthogonal substitutions, and makes each $\mathrm{act}\,\nu\,c\,d$ skew, $\beta(\mathrm{act}\,\nu\,c\,d\,P,Q)=-\beta(P,\mathrm{act}\,\nu\,c\,d\,Q)$. Then every $P\in W$ vanishes at every orthogonal matrix.
--
--   In the polynomial compact-picture model used for the Langlands–Tunnell input, $W$ modulo the polynomials vanishing on the orthogonal group is a $(\mathfrak{g},K)$-submodule of a minimal principal series of $GL_3(\mathbb{R})$ with the indicated infinitesimal character and sign character, and $\beta$ would descend to a positive invariant Hermitian form; the statement says that no such $W$ has a polynomial not vanishing on $O(3)$, i.e. the odd sign class carries no positive invariant form. It is used by [`LanglandsTunnell.CubicInduction.forall_apply_orthogonal_eq_zero_of_signIsotypic_odd_of_inducedPicture_package`](thm.html#LanglandsTunnell.CubicInduction.forall_apply_orthogonal_eq_zero_of_signIsotypic_odd_of_inducedPicture_package).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_forall_eval_orthogonal_eq_zero_of_odd_signClass_of_positive_actSkew_form.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem LanglandsTunnell.CubicInduction.forall_eval_orthogonal_eq_zero_of_odd_signClass_of_positive_actSkew_form
    (σ σ₃ : ℝ) (b₀ c₀ : Fin 3) (hb₀ : b₀ ≠ 0) (hc₀ : c₀ ≠ 0) (hbc : b₀ ≠ c₀)
    (ν : Fin 3 → ℂ) (hν0 : ν 0 = -1 / 2 + σ * Complex.I) (hνb : ν b₀ = 1 / 2 + σ * Complex.I)
    (hνc : ν c₀ = σ₃ * Complex.I)
    (ε : Fin 3 → Fin 2) (hodd : ε 0 ≠ ε b₀)
    (W : Submodule ℂ (MvPolynomial (Fin 3 × Fin 3) ℂ))
    (β : MvPolynomial (Fin 3 × Fin 3) ℂ → MvPolynomial (Fin 3 × Fin 3) ℂ → ℂ) :
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
    (∀ (z : ℂ), ∀ P₁ ∈ W, ∀ P₂ ∈ W, ∀ Q ∈ W, β (z • P₁ + P₂) Q = z * β P₁ Q + β P₂ Q) →
    (∀ P ∈ W, ∀ Q ∈ W, β Q P = (starRingEnd ℂ) (β P Q)) →
    (∀ P ∈ W, (∀ o : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) → MvPolynomial.eval (fun ij : Fin 3 × Fin 3 => ((o ij.1 ij.2 : ℝ) : ℂ)) P = 0) → ∀ Q ∈ W, β P Q = 0) →
    (∀ P ∈ W, (∃ o : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) ∧ MvPolynomial.eval (fun ij : Fin 3 × Fin 3 => ((o ij.1 ij.2 : ℝ) : ℂ)) P ≠ 0) → 0 < (β P P).re) →
    (∀ P ∈ W, ∀ Q ∈ W, ∀ r : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, ∑ a : Fin 3, r a i * r a j = if i = j then 1 else 0) →
        β (MvPolynomial.aeval (fun ij : Fin 3 × Fin 3 =>
            ∑ c : Fin 3, MvPolynomial.X (ij.1, c) * MvPolynomial.C ((r c ij.2 : ℝ) : ℂ)) P)
          (MvPolynomial.aeval (fun ij : Fin 3 × Fin 3 =>
            ∑ c : Fin 3, MvPolynomial.X (ij.1, c) * MvPolynomial.C ((r c ij.2 : ℝ) : ℂ)) Q) = β P Q) →
    (∀ P ∈ W, ∀ Q ∈ W, ∀ c d : Fin 3, β (act ν c d P) Q = -β P (act ν c d Q)) →
    ∀ P ∈ W, ∀ o : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) → MvPolynomial.eval (fun ij : Fin 3 × Fin 3 => ((o ij.1 ij.2 : ℝ) : ℂ)) P = 0 := by sorry
