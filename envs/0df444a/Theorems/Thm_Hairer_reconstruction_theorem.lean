-- Prove2me | Theorems.Thm_Hairer_reconstruction_theorem
-- name    : Hairer.reconstruction_theorem
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-12T20:39:32.470801+00:00
-- url     : https://prove2.me/theorems/61b3fefd-925f-402d-90a4-3f74d93f9d6a
-- title:
--   Reconstruction theorem (Hairer, Theorem 3.10) for $\gamma>0$
-- statement:
--   **Theorem 3.10 of Hairer (2014), the reconstruction theorem, in the case $\gamma>0$.**
--
--   Let $(A,T,G)$ be a regularity structure, let $(\Pi,\Gamma)$ be a model for it on
--   $\mathbb{R}^d$ with scaling $s$, let $\alpha = \min A$ with $\alpha<0$, and let $r$ be the
--   order of test functions attached to $A$. Then for every $\gamma>0$ and every modelled
--   distribution $f \in \mathcal{D}^\gamma$ there is a distribution $\mathcal{R}f$ with the
--   following three properties.
--
--   1. $\mathcal{R}f \in \mathcal{C}^\alpha_s$.
--   2. For every compact set $K$ there is a constant $C$ such that
--   $$ \big|(\mathcal{R}f - \Pi_x f(x))(S^{\delta}_{s,x}\eta)\big| \le C\,\delta^{\gamma} $$
--   uniformly over $x \in K$, $\delta \in (0,1]$ and $\eta \in \mathcal{B}^r_{s,0}$.
--   3. It is the only distribution with property 2: any $\zeta$ satisfying the same family of
--   bounds equals $\mathcal{R}f$.
--
--   In words: a coherent family of local expansions $x \mapsto \Pi_x f(x)$, coherent in the sense
--   encoded by $f \in \mathcal{D}^\gamma$, is the local description of one single distribution,
--   uniquely determined by the requirement that the approximation error at scale $\delta$ around
--   each point be of order $\delta^\gamma$.
-- source:
--   M. Hairer, A theory of regularity structures, Inventiones Mathematicae 198 (2014) 269-504, arXiv:1303.5113 (v4), Theorem 3.10, p. 31, bound (3.3)

import Definitions.Def_Hairer_Model

set_option autoImplicit false

open scoped Classical DirectSum

noncomputable section

namespace Hairer

/-- **Theorem 3.10 (Reconstruction theorem), Hairer 2014**, in the case `γ > 0`.

For a model `(Π, Γ)` of a regularity structure with `α = min A < 0`, every modelled
distribution `f ∈ D^γ` with `γ > 0` is the local description of a unique distribution
`Rf`, which moreover belongs to `C^α_s`: there is a unique `ξ` such that on every
compact set `|(ξ - Π_x f(x))(S^δ_{s,x} η)| ≲ δ^γ`, uniformly over `x` in the compact,
`δ ∈ (0,1]` and test functions `η ∈ B^r_{s,0}`. -/
theorem reconstruction_theorem
    {d : ℕ} {s : Fin d → ℕ} (hs : IsScaling s)
    {A : Set ℝ} {E : A → Type} [∀ a : A, NormedAddCommGroup (E a)]
    [∀ a : A, NormedSpace ℝ (E a)]
    {G : Subgroup (ModelSpace A E ≃ₗ[ℝ] ModelSpace A E)} {one : ModelSpace A E}
    (hT : IsRegularityStructure A E G one)
    {r : ℕ} {Pi : Pt d → ModelSpace A E →ₗ[ℝ] Distrib d}
    {Gam : Pt d → Pt d → ModelSpace A E ≃ₗ[ℝ] ModelSpace A E}
    (hmod : IsModel s r G Pi Gam)
    {α : ℝ} (hα : IsLeast A α) (hαneg : α < 0)
    {γ : ℝ} (hγ : 0 < γ)
    {f : Pt d → ModelSpace A E} (hf : IsModelled s γ Gam f) :
    ∃ ξ : Distrib d,
      MemCalpha s α ξ ∧
      (∀ K : Set (Pt d), IsCompact K → ∃ C : ℝ, ∀ x ∈ K, ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
        ∀ η : Pt d → ℝ, IsTestBall s r η →
          |(ξ - Pi x (f x)).eval (scaledTest s δ x η)| ≤ C * δ ^ γ) ∧
      (∀ ζ : Distrib d,
        (∀ K : Set (Pt d), IsCompact K → ∃ C : ℝ, ∀ x ∈ K, ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
          ∀ η : Pt d → ℝ, IsTestBall s r η →
            |(ζ - Pi x (f x)).eval (scaledTest s δ x η)| ≤ C * δ ^ γ) → ζ = ξ) := by
  sorry

end Hairer
