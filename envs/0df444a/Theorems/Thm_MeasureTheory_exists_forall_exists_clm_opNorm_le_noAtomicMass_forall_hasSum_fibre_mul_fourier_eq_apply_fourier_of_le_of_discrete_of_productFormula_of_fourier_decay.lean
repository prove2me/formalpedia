-- Prove2me | Theorems.Thm_MeasureTheory_exists_forall_exists_clm_opNorm_le_noAtomicMass_forall_hasSum_fibre_mul_fourier_eq_apply_fourier_of_le_of_discrete_of_productFormula_of_fourier_decay
-- name    : MeasureTheory.exists_forall_exists_clm_opNorm_le_noAtomicMass_forall_hasSum_fibre_mul_fourier_eq_apply_fourier_of_le_of_discrete_of_productFormula_of_fourier_decay
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.429051+00:00
-- url     : https://prove2.me/theorems/7aee89dd-79ba-5557-9772-2dee8a6958a3
-- title:
--   Winding measures with sublattice-uniform total variation bound
-- statement:
--   Fix natural numbers $r,d,c$, a discrete additive subgroup $\Lambda \le \mathbb{R}^r \times \mathbb{Z}^d$ (discreteness being carried by the subspace topology on $\Lambda$), an $\mathbb{R}$-linear form $s$ on $\mathbb{R}^r$ and a nonzero $\omega \in \mathbb{R}^d$ such that $s(x_1) = \sum_i \omega_i (x_2)_i$ for every $x = (x_1,x_2) \in \Lambda$. Then there exists a real constant $K$ with the following property, uniformly in all the data listed next: for every subgroup $\Lambda' \le \Lambda$, every additive homomorphism $\chi : \Lambda' \to (\mathbb{R}/\mathbb{Z})^c$ (using $\mathrm{AddCircle}\ 1$), every $m \in \mathbb{Z}^c$, every $\theta_0 \in (\mathbb{R}/\mathbb{Z})^c$, every continuous integrable $\Psi : \mathbb{R}^r \to \mathbb{C}$ and every real $C$ such that $\|\Psi(x)\| \le C \prod_i (1+|x_i|)^{-2}$ for all $x$ and $\bigl\| \int_{\mathbb{R}^r} e^{-2\pi i \sum_i \xi_i x_i} \Psi(x)\,dx \bigr\| \le C \prod_i (1+|\xi_i|)^{-2}$ for all $\xi$, and all shifts $x_0 \in \mathbb{R}^r$, $n_0 \in \mathbb{Z}^d$, there is a continuous $\mathbb{C}$-linear functional $\mu$ on $C((\mathbb{R}/\mathbb{Z})^d, \mathbb{C})$ with: (i) $\|\mu\| \le K\,C$; (ii) no atomic mass, i.e. for each $\tau$ and each $\varepsilon > 0$ there are open sets $U_i \ni \tau_i$ with $\|\mu(g)\| < \varepsilon$ for every continuous $g$ bounded by $1$ in modulus and vanishing at every $\theta$ with some $\theta_i \notin U_i$; and (iii) for every $n \in \mathbb{Z}^d$ and every continuous $e$ with $e(\theta) = \prod_i \mathrm{fourier}(n_i)(\theta_i)$, the family indexed by $\gamma \in \Lambda'$ whose term is $\Psi(x_0 + \gamma_1) \prod_j \mathrm{fourier}(m_j)(\theta_{0,j} + \chi(\gamma)_j)$ when $\gamma_2 + n_0 = n$ and $0$ otherwise is summable with sum $\mu(e)$.
--
--   This is the quantitative form of the twisted product-window winding measure: the Fourier coefficients of $\mu$ along $(\mathbb{R}/\mathbb{Z})^d$ are the lattice sums of a rapidly decaying window twisted by a character of $\Lambda'$, and the total variation bound $K\,C$ holds with $K$ independent of the sublattice $\Lambda' \le \Lambda$, of the twist $(\chi, m, \theta_0)$ and of the shifts $(x_0,n_0)$. The uniformity is what allows countably many such measures to be summed, and it is used in this form by [`AutomorphicForm.WindingDatum.exists_clm_noAtomicMass_forall_apply_fourier_eq_coeff`](thm.html#AutomorphicForm.WindingDatum.exists_clm_noAtomicMass_forall_apply_fourier_eq_coeff).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MeasureTheory_exists_forall_exists_clm_opNorm_le_noAtomicMass_forall_hasSum_fibre_mul_fourier_eq_apply_fourier_of_le_of_discrete_of_productFormula_of_fourier_decay.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory

theorem MeasureTheory.exists_forall_exists_clm_opNorm_le_noAtomicMass_forall_hasSum_fibre_mul_fourier_eq_apply_fourier_of_le_of_discrete_of_productFormula_of_fourier_decay
    (r d c : ℕ) (Λ : AddSubgroup ((Fin r → ℝ) × (Fin d → ℤ)))
    (hΛ : DiscreteTopology Λ)
    (s : (Fin r → ℝ) →ₗ[ℝ] ℝ) (ω : Fin d → ℝ) (hω : ω ≠ 0)
    (hpf : ∀ x ∈ Λ, s x.1 = ∑ i, ω i * (x.2 i : ℝ)) :
    ∃ K : ℝ, ∀ (Λ' : AddSubgroup ((Fin r → ℝ) × (Fin d → ℤ))) (hΛ' : Λ' ≤ Λ)
      (χ : Λ' →+ (Fin c → AddCircle (1 : ℝ))) (m : Fin c → ℤ) (θ₀ : Fin c → AddCircle (1 : ℝ))
      (Ψ : (Fin r → ℝ) → ℂ) (hΨc : Continuous Ψ) (hΨi : Integrable Ψ) (C : ℝ)
      (hΨd : ∀ x : Fin r → ℝ, ‖Ψ x‖ ≤ C * ∏ i, (1 + |x i|)⁻¹ ^ 2)
      (hΨhatd : ∀ ξ : Fin r → ℝ,
        ‖∫ x : Fin r → ℝ, Complex.exp (-(2 * Real.pi * Complex.I * ((∑ i, ξ i * x i : ℝ) : ℂ))) * Ψ x‖ ≤
          C * ∏ i, (1 + |ξ i|)⁻¹ ^ 2)
      (x₀ : Fin r → ℝ) (n₀ : Fin d → ℤ),
    ∃ μ : C((Fin d → AddCircle (1 : ℝ)), ℂ) →L[ℂ] ℂ,
      ‖μ‖ ≤ K * C ∧
      (∀ (τ : Fin d → AddCircle (1 : ℝ)), ∀ ε > (0 : ℝ),
        ∃ U : Fin d → Set (AddCircle (1 : ℝ)), (∀ i, IsOpen (U i) ∧ τ i ∈ U i) ∧
          ∀ g : C((Fin d → AddCircle (1 : ℝ)), ℂ),
            (∀ θ, (∃ i, θ i ∉ U i) → g θ = 0) → (∀ θ, ‖g θ‖ ≤ 1) → ‖μ g‖ < ε) ∧
      ∀ (n : Fin d → ℤ) (e : C((Fin d → AddCircle (1 : ℝ)), ℂ)),
        (∀ θ, e θ = ∏ i, fourier (n i) (θ i)) →
        HasSum (fun γ : Λ' => if (γ : (Fin r → ℝ) × (Fin d → ℤ)).2 + n₀ = n
            then Ψ (x₀ + (γ : (Fin r → ℝ) × (Fin d → ℤ)).1) * ∏ j, fourier (m j) (θ₀ j + χ γ j) else 0) (μ e) := by sorry
