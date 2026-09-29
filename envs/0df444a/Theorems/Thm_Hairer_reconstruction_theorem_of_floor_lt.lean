-- Prove2me | Theorems.Thm_Hairer_reconstruction_theorem_of_floor_lt
-- name    : Hairer.reconstruction_theorem_of_floor_lt
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T21:33:57.613856+00:00
-- url     : https://prove2.me/theorems/605f1696-64ee-47d3-954f-b80ab15bde89
-- title:
--   Reconstruction with negative Hölder regularity under a strict floor condition
-- statement:
--   Let $(A,T,G)$ be a regularity structure, $(\Pi,\Gamma)$ a model, and $f$ a modelled distribution of regularity $\gamma>0$. Suppose $\alpha<0$ is a lower bound for $A$ and $\lfloor\alpha\rfloor<a$ for every $a\in A$. There exists a distribution $\xi\in\mathcal C_s^\alpha$ such that, for every compact set $K$, there is a constant $C_K$ with
--
--   $$|\langle\xi-\Pi_x f(x),S^\delta_{s,x}\eta\rangle|\le C_K\delta^\gamma\qquad(x\in K,\ 0<\delta\le1,\ \eta\in\mathcal B_s^r).$$
--
--   Every distribution satisfying this reconstruction estimate equals $\xi$. The strict floor condition holds at a noninteger least negative homogeneity, and at every negative exponent strictly below a lower bound for $A$. This result does not cover an integer least homogeneity at the same exponent.
-- source:
--   Restricted form of M. Hairer, A theory of regularity structures (2014), Theorem 3.10, with an explicit strict floor condition for the formal test-order definitions.

import Definitions.Def_Hairer_Model
open BigOperators Hairer
noncomputable section

theorem Hairer.reconstruction_theorem_of_floor_lt
    {d : ℕ} {s : Fin d → ℕ} (hs : IsScaling s) {γ : ℝ} (hγ : 0 < γ)
    {A : Set ℝ} {E : A → Type} [∀ a : A, NormedAddCommGroup (E a)]
    [∀ a : A, NormedSpace ℝ (E a)]
    {G : Subgroup (ModelSpace A E ≃ₗ[ℝ] ModelSpace A E)} {one : ModelSpace A E}
    (hT : IsRegularityStructure A E G one)
    {r : ℕ} {Pi : Pt d → ModelSpace A E →ₗ[ℝ] Distrib d}
    {Gam : Pt d → Pt d → ModelSpace A E ≃ₗ[ℝ] ModelSpace A E}
    (hmod : IsModel s r G Pi Gam)
    {α : ℝ} (hα : α < 0) (hlower : ∀ a ∈ A, α ≤ a)
    (hfloor : ∀ a ∈ A, (⌊α⌋ : ℝ) < a)
    {f : Pt d → ModelSpace A E} (hf : IsModelled s γ Gam f) :
    ∃ ξ : Distrib d, MemCalpha s α ξ ∧
      (∀ K : Set (Pt d), IsCompact K → ∃ C : ℝ, ∀ x ∈ K,
        ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ η : Pt d → ℝ, IsTestBall s r η →
          |(ξ - Pi x (f x)).eval (scaledTest s δ x η)| ≤ C * δ ^ γ) ∧
      (∀ ζ : Distrib d,
        (∀ K : Set (Pt d), IsCompact K → ∃ C : ℝ, ∀ x ∈ K,
          ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ η : Pt d → ℝ, IsTestBall s r η →
            |(ζ - Pi x (f x)).eval (scaledTest s δ x η)| ≤ C * δ ^ γ) → ζ = ξ) := by sorry
