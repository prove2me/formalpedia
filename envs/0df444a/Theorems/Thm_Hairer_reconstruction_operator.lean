-- Prove2me | Theorems.Thm_Hairer_reconstruction_operator
-- name    : Hairer.reconstruction_operator
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-12T20:43:07.534823+00:00
-- url     : https://prove2.me/theorems/db310e6f-3fb9-4fd0-a864-08cd01425863
-- title:
--   Existence of a linear reconstruction operator for arbitrary $\gamma$
-- statement:
--   **Existence part of Hairer's Theorem 3.10 for an arbitrary exponent $\gamma \in \mathbb{R}$.**
--
--   For a model $(\Pi,\Gamma)$ of a regularity structure with $\alpha = \min A < 0$, and for any
--   $\gamma \in \mathbb{R}$, there is a reconstruction map $\mathcal{R}$, defined on modelled
--   distributions, such that:
--
--   - $\mathcal{R}$ is linear on $\mathcal{D}^\gamma$, that is $\mathcal{R}(f+g) = \mathcal{R}f
--   + \mathcal{R}g$ and $\mathcal{R}(cf) = c\,\mathcal{R}f$ for modelled distributions $f,g$ and
--   scalars $c$;
--   - $\mathcal{R}f \in \mathcal{C}^\alpha_s$ for every $f \in \mathcal{D}^\gamma$;
--   - for every $f \in \mathcal{D}^\gamma$ and every compact $K$ there is a constant $C$ with
--   $$ \big|(\mathcal{R}f - \Pi_x f(x))(S^{\delta}_{s,x}\eta)\big| \le C\,\delta^{\gamma} $$
--   uniformly over $x \in K$, $\delta \in (0,1]$ and $\eta \in \mathcal{B}^r_{s,0}$.
--
--   For $\gamma \le 0$ the bound no longer determines $\mathcal{R}f$, so existence of a linear
--   choice is the substantive assertion; for $\gamma>0$ it complements the uniqueness statement.
-- source:
--   M. Hairer, A theory of regularity structures, Inventiones Mathematicae 198 (2014) 269-504, arXiv:1303.5113 (v4), Theorem 3.10, p. 31 (existence of the continuous linear map for every $\gamma \in \mathbb{R}$)

import Definitions.Def_Hairer_Model

set_option autoImplicit false

open scoped Classical DirectSum

noncomputable section

namespace Hairer

/-- **Theorem 3.10 (existence of the reconstruction operator), Hairer 2014**, for an
arbitrary exponent `γ ∈ ℝ`.

There is a *linear* reconstruction map `R` defined on modelled distributions, with
values in `C^α_s` where `α = min A`, such that for every `f ∈ D^γ` and every compact
set `K` one has `|(Rf - Π_x f(x))(S^δ_{s,x} η)| ≲ δ^γ`, uniformly over `x ∈ K`,
`δ ∈ (0,1]` and `η ∈ B^r_{s,0}`. Unlike the case `γ > 0`, for `γ ≤ 0` this bound no
longer determines `R` uniquely. -/
theorem reconstruction_operator
    {d : ℕ} {s : Fin d → ℕ} (hs : IsScaling s)
    {A : Set ℝ} {E : A → Type} [∀ a : A, NormedAddCommGroup (E a)]
    [∀ a : A, NormedSpace ℝ (E a)]
    {G : Subgroup (ModelSpace A E ≃ₗ[ℝ] ModelSpace A E)} {one : ModelSpace A E}
    (hT : IsRegularityStructure A E G one)
    {r : ℕ} {Pi : Pt d → ModelSpace A E →ₗ[ℝ] Distrib d}
    {Gam : Pt d → Pt d → ModelSpace A E ≃ₗ[ℝ] ModelSpace A E}
    (hmod : IsModel s r G Pi Gam)
    {α : ℝ} (hα : IsLeast A α) (hαneg : α < 0) (γ : ℝ) :
    ∃ R : (Pt d → ModelSpace A E) → Distrib d,
      (∀ f g : Pt d → ModelSpace A E, IsModelled s γ Gam f → IsModelled s γ Gam g →
        R (f + g) = R f + R g) ∧
      (∀ (c : ℝ) (f : Pt d → ModelSpace A E), IsModelled s γ Gam f →
        R (c • f) = c • R f) ∧
      (∀ f : Pt d → ModelSpace A E, IsModelled s γ Gam f →
        MemCalpha s α (R f) ∧
        ∀ K : Set (Pt d), IsCompact K → ∃ C : ℝ, ∀ x ∈ K, ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
          ∀ η : Pt d → ℝ, IsTestBall s r η →
            |(R f - Pi x (f x)).eval (scaledTest s δ x η)| ≤ C * δ ^ γ) := by
  sorry

end Hairer
