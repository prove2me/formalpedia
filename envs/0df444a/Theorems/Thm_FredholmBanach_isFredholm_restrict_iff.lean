-- Prove2me | Theorems.Thm_FredholmBanach_isFredholm_restrict_iff
-- name    : FredholmBanach.isFredholm_restrict_iff
-- status  : Open
-- author  : @Mazecto
-- created : 2026-10-09T15:39:25.21241+00:00
-- url     : https://prove2.me/theorems/d019cd3a-49e7-41eb-b3ea-d462e0c635d0
-- title:
--   Restricting an operator to closed subspaces of finite codimension preserves the Fredholm property and shifts the index by the codimensions
-- statement:
--   Let $\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$ and let $E$, $F$ be Banach spaces over $\mathbb{K}$. Let $u:E\to F$ be a bounded linear map, and let $E_1\subset E$ and $F_1\subset F$ be closed linear subspaces with $E/E_1$ and $F/F_1$ finite-dimensional and $u(E_1)\subset F_1$. Let $u_1:E_1\to F_1$ be the restriction of $u$. Then $u$ is Fredholm if and only if $u_1$ is Fredholm, and in that case
--   $$\operatorname{ind}u-\operatorname{ind}u_1=\dim(E/E_1)-\dim(F/F_1),$$
--   where $\operatorname{ind}u=\dim\operatorname{Ker}u-\dim(F/\operatorname{Im}u)$ and likewise for $u_1$.
-- source:
--   N. Bourbaki, Théories spectrales, Chapitres III à V, Springer (2023), https://doi.org/10.1007/978-3-031-19505-1, Chapitre III, § 3, n° 3, Proposition 3 and formula (5), p. TS III.44 (with the opposite sign of the index)

import Definitions.Def_FredholmBanach_Setting

namespace FredholmBanach

open Topology

/-- Bourbaki, *Théories spectrales*, III, § 3, n° 3, Proposition 3 and formula (5) (TS III.44):
let `E₁ ⊆ E`, `F₁ ⊆ F` be closed subspaces of finite codimension with `u (E₁) ⊆ F₁`, and let
`u₁ : E₁ → F₁` be the restriction. Then `u` is Fredholm if and only if `u₁` is, and then
`ind u - ind u₁ = codim E₁ - codim F₁` (with the sign convention `ind = dim Ker - dim Coker`). -/
theorem isFredholm_restrict_iff {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
    (u : E →L[𝕜] F) (E₁ : Submodule 𝕜 E) (F₁ : Submodule 𝕜 F)
    (hE₁ : IsClosed (E₁ : Set E)) (hF₁ : IsClosed (F₁ : Set F))
    (hE₁f : FiniteDimensional 𝕜 (E ⧸ E₁)) (hF₁f : FiniteDimensional 𝕜 (F ⧸ F₁))
    (h : Set.MapsTo u E₁ F₁) :
    (u.IsFredholm ↔ (u.restrict h).IsFredholm) ∧
      (u.IsFredholm → index u - index (u.restrict h) =
        (Module.finrank 𝕜 (E ⧸ E₁) : ℤ) - (Module.finrank 𝕜 (F ⧸ F₁) : ℤ)) := by sorry

end FredholmBanach
