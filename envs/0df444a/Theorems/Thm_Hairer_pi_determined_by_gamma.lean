-- Prove2me | Theorems.Thm_Hairer_pi_determined_by_gamma
-- name    : Hairer.pi_determined_by_gamma
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-12T20:46:02.416717+00:00
-- url     : https://prove2.me/theorems/d9e5e268-9d8a-4af4-8e74-09a0ac484e88
-- title:
--   $\Pi$ on $T_\nu$ is determined by $\Gamma$ (Hairer, Proposition 3.31)
-- statement:
--   **Proposition 3.31 of Hairer (2014), determinacy statement.**
--
--   Let $\nu>0$ be an element of the index set $A$. The action of $\Pi$ on the homogeneous
--   component $T_\nu$ is completely determined by $\Gamma$ together with the action of $\Pi$ on
--   lower homogeneities: if $(\Pi,\Gamma)$ and $(\Pi',\Gamma)$ are two models for the same
--   regularity structure, with the *same* $\Gamma$, and if $\Pi_x a = \Pi'_x a$ for every $x$ and
--   every $a \in T_b$ with $b<\nu$, then $\Pi_x a = \Pi'_x a$ for every $x$ and every
--   $a \in T_\nu$.
--
--   The mechanism is that for positive homogeneity the distribution $\Pi_x a$ is forced to be the
--   reconstruction of the modelled distribution $y \mapsto \Gamma_{yx}a$ minus its lower-order
--   part, so no freedom is left once $\Gamma$ and the lower levels are fixed. Hairer states the
--   result together with the quantitative bound (3.42) on the $T_\nu$ component of $\Pi$ in terms
--   of the model norms; the content formalized here is the determinacy assertion.
-- source:
--   M. Hairer, A theory of regularity structures, Inventiones Mathematicae 198 (2014) 269-504, arXiv:1303.5113 (v4), Proposition 3.31, p. 44 (with the bound (3.42))

import Definitions.Def_Hairer_Model

set_option autoImplicit false

open scoped Classical DirectSum

noncomputable section

namespace Hairer

/-- **Proposition 3.31, Hairer 2014.**

For `ν > 0`, the action of `Π` on `T_ν` is completely determined by its action on
`T_{<ν}` together with `Γ`: two models for the same regularity structure that share
the same `Γ` and whose `Π`-maps agree on all homogeneities strictly below `ν` also
agree on `T_ν`. -/
theorem pi_determined_by_gamma
    {d : ℕ} {s : Fin d → ℕ} (hs : IsScaling s)
    {A : Set ℝ} {E : A → Type} [∀ a : A, NormedAddCommGroup (E a)]
    [∀ a : A, NormedSpace ℝ (E a)]
    {G : Subgroup (ModelSpace A E ≃ₗ[ℝ] ModelSpace A E)} {one : ModelSpace A E}
    (hT : IsRegularityStructure A E G one)
    {r : ℕ} {Pi Pi' : Pt d → ModelSpace A E →ₗ[ℝ] Distrib d}
    {Gam : Pt d → Pt d → ModelSpace A E ≃ₗ[ℝ] ModelSpace A E}
    (hmod : IsModel s r G Pi Gam) (hmod' : IsModel s r G Pi' Gam)
    {ν : ℝ} (hν : 0 < ν) (hνA : ν ∈ A)
    (hlow : ∀ (b : A), (b : ℝ) < ν → ∀ (a : E b), ∀ x : Pt d,
      Pi x (incl b a) = Pi' x (incl b a)) :
    ∀ (a : E (⟨ν, hνA⟩ : A)), ∀ x : Pt d,
      Pi x (incl (⟨ν, hνA⟩ : A) a) = Pi' x (incl (⟨ν, hνA⟩ : A) a) := by
  sorry

end Hairer
