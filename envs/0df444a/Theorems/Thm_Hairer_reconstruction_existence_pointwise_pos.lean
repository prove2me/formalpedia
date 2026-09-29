-- Prove2me | Theorems.Thm_Hairer_reconstruction_existence_pointwise_pos
-- name    : Hairer.reconstruction_existence_pointwise_pos
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-19T12:04:32.264483+00:00
-- url     : https://prove2.me/theorems/115a07e0-08bf-41e4-9b74-343e158943b8
-- title:
--   Existence of the reconstruction of a modelled distribution for $\gamma>0$
-- statement:
--   **Existence half of Hairer's Theorem 3.10 for a positive exponent, stated for one modelled distribution.**
--
--   Let $\mathscr T=(A,T,G)$ be a regularity structure, let $(\Pi,\Gamma)$ be a model for it on $\mathbb R^d$ with scaling $s$ and test order $r$, let $\alpha=\min A<0$, and let $\gamma>0$. Then for every modelled distribution $f\in\mathcal D^\gamma$ there exists a distribution $\xi$ such that
--
--   $$\xi\in\mathcal C^{\alpha}_s,\qquad \bigl|(\xi-\Pi_xf(x))(S^{\delta}_{s,x}\eta)\bigr|\;\le\;C\,\delta^{\gamma},$$
--
--   the second bound holding, for every compact set $K$ with a constant $C=C(K,f)$, uniformly over $x\in K$, $\delta\in(0,1]$ and all test functions $\eta\in\mathcal B^r_{s,0}$.
--
--   Only the existence of $\xi$ for a *single* $f$ is asserted. For $\gamma>0$ the displayed bound determines $\xi$ uniquely, so the linearity of the assignment $f\mapsto\xi$ — which is part of the statement of Theorem 3.10 — is a formal consequence of uniqueness and is deliberately not included here. This is the analytic core of the theorem in the positive range: Hairer obtains $\xi$ as the limit of a convergent multiscale approximation built from a wavelet multiresolution analysis adapted to the scaling $s$ (§3.1).
-- source:
--   M. Hairer, A theory of regularity structures, Invent. Math. 198 (2014) 269-504, arXiv:1303.5113 (v4), Theorem 3.10, p. 31 (existence half, case gamma > 0; construction in Section 3.1)

import Definitions.Def_Hairer_Model

set_option autoImplicit false

open scoped Classical DirectSum

noncomputable section

namespace Hairer

/-- **Theorem 3.10 (existence of the reconstruction), Hairer 2014**, in the case `γ > 0`,
stated for a single modelled distribution.

For `f ∈ D^γ` with `γ > 0` there is a distribution `ξ ∈ C^α_s` such that, on every
compact set `K`, `|(ξ - Π_x f(x))(S^δ_{s,x} η)| ≲ δ^γ` uniformly over `x ∈ K`,
`δ ∈ (0,1]` and `η ∈ B^r_{s,0}`. For `γ > 0` such a `ξ` is unique, so the linearity of
`f ↦ ξ` is automatic and is not part of this statement. -/
theorem reconstruction_existence_pointwise_pos
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
      ∀ K : Set (Pt d), IsCompact K → ∃ C : ℝ, ∀ x ∈ K, ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
        ∀ η : Pt d → ℝ, IsTestBall s r η →
          |(ξ - Pi x (f x)).eval (scaledTest s δ x η)| ≤ C * δ ^ γ := by
  sorry

end Hairer
