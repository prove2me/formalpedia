-- Prove2me | Theorems.Thm_Hairer_reconstruction_existence_pointwise_nonpos
-- name    : Hairer.reconstruction_existence_pointwise_nonpos
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-19T12:15:59.288606+00:00
-- url     : https://prove2.me/theorems/a1aef1ca-113d-4680-a38f-cf663cef85ba
-- title:
--   Existence of the reconstruction of a modelled distribution for $\alpha<\gamma\le 0$
-- statement:
--   **Existence half of Hairer's Theorem 3.10 in the range $\alpha<\gamma\le 0$, stated for one modelled distribution.**
--
--   Let $\mathscr T=(A,T,G)$ be a regularity structure, let $(\Pi,\Gamma)$ be a model for it on $\mathbb R^d$ with scaling $s$ and test order $r$, let $\alpha=\min A<0$, and let $\alpha<\gamma\le 0$. Then for every modelled distribution $f\in\mathcal D^\gamma$ there exists a distribution $\xi$ with
--
--   $$\xi\in\mathcal C^{\alpha}_s,\qquad \bigl|(\xi-\Pi_xf(x))(S^{\delta}_{s,x}\eta)\bigr|\;\le\;C\,\delta^{\gamma},$$
--
--   the second bound holding, for every compact set $K$ with a constant $C=C(K,f)$, uniformly over $x\in K$, $\delta\in(0,1]$ and $\eta\in\mathcal B^r_{s,0}$.
--
--   For $\gamma\le 0$ the bound no longer determines $\xi$, which is why Theorem 3.10 also asserts that a *linear* choice $f\mapsto\mathcal Rf$ exists. That linearity is not part of this statement: once each modelled distribution is reconstructed individually, the pairs $(f,\xi)$ satisfying the two displayed conditions form a linear subspace that surjects onto $\mathcal D^\gamma$, and a linear section of that surjection turns the pointwise statement into a linear operator. What remains here is therefore the analytic content of §3.1 in the non-positive range: the multiscale construction of a distribution matching the local jets $\Pi_xf(x)$ to order $\delta^\gamma$.
--
--   The complementary range $\gamma\le\alpha$ is excluded because it is degenerate: there every modelled distribution vanishes identically.
-- source:
--   M. Hairer, A theory of regularity structures, Invent. Math. 198 (2014) 269-504, arXiv:1303.5113 (v4), Theorem 3.10, p. 31 (existence half in the non-positive range; construction in Section 3.1)

import Definitions.Def_Hairer_Model

set_option autoImplicit false

open scoped Classical DirectSum

noncomputable section

namespace Hairer

/-- **Theorem 3.10 (existence of the reconstruction), Hairer 2014**, in the case
`α < γ ≤ 0`, stated for a single modelled distribution.

For `f ∈ D^γ` there is a distribution `ξ ∈ C^α_s` such that, on every compact set `K`,
`|(ξ - Π_x f(x))(S^δ_{s,x} η)| ≲ δ^γ` uniformly over `x ∈ K`, `δ ∈ (0,1]` and
`η ∈ B^r_{s,0}`. For `γ ≤ 0` this bound no longer determines `ξ`; no linearity in `f` is
asserted here, a linear choice being obtainable from the pointwise statement.

The range `γ ≤ α` is excluded because it is degenerate: there the only modelled
distribution is `f = 0`. -/
theorem reconstruction_existence_pointwise_nonpos
    {d : ℕ} {s : Fin d → ℕ} (hs : IsScaling s)
    {A : Set ℝ} {E : A → Type} [∀ a : A, NormedAddCommGroup (E a)]
    [∀ a : A, NormedSpace ℝ (E a)]
    {G : Subgroup (ModelSpace A E ≃ₗ[ℝ] ModelSpace A E)} {one : ModelSpace A E}
    (hT : IsRegularityStructure A E G one)
    {r : ℕ} {Pi : Pt d → ModelSpace A E →ₗ[ℝ] Distrib d}
    {Gam : Pt d → Pt d → ModelSpace A E ≃ₗ[ℝ] ModelSpace A E}
    (hmod : IsModel s r G Pi Gam)
    {α : ℝ} (hα : IsLeast A α) (hαneg : α < 0)
    {γ : ℝ} (hγα : α < γ) (hγ : γ ≤ 0)
    {f : Pt d → ModelSpace A E} (hf : IsModelled s γ Gam f) :
    ∃ ξ : Distrib d,
      MemCalpha s α ξ ∧
      ∀ K : Set (Pt d), IsCompact K → ∃ C : ℝ, ∀ x ∈ K, ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
        ∀ η : Pt d → ℝ, IsTestBall s r η →
          |(ξ - Pi x (f x)).eval (scaledTest s δ x η)| ≤ C * δ ^ γ := by
  sorry

end Hairer
