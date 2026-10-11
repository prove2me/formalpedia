-- Prove2me | Theorems.Thm_FredholmBanach_isFredholm_index_of_bijective_coprod
-- name    : FredholmBanach.isFredholm_index_of_bijective_coprod
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-10T22:25:35.184782+00:00
-- url     : https://prove2.me/theorems/c4d03c77-ce24-4a91-b0ae-f3468ffc2a6d
-- title:
--   Fredholm property and index of $v$ when $(x,c)\mapsto v(x)+c$ is a bijection $E_0\times C\to F$
-- statement:
--   Let $\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$, let $E$, $F$ be Banach spaces over $\mathbb{K}$, and let $v:E\to F$ be a bounded linear map. Let $E_0\subseteq E$ be a linear subspace of finite codimension and $C\subseteq F$ a finite-dimensional linear subspace. If the map
--   $$E_0\times C\to F,\qquad (x,c)\mapsto v(x)+c$$
--   is bijective, then $v$ is a Fredholm operator and
--   $$\operatorname{ind}v=\dim(E/E_0)-\dim C,$$
--   where $\operatorname{ind}v=\dim\operatorname{Ker}v-\dim(F/\operatorname{Im}v)$.
--
--   This gives a way to recognize a Fredholm operator, and to read off its index, from a bijective map obtained by restricting $v$ to a subspace of finite codimension and adding a finite-dimensional subspace of the target. It is reusable for statements about Fredholm operators near a given one and about perturbations.
--
--   **Formalization Note.** $E_0$ is an arbitrary `Submodule 𝕜 E` (no closedness assumption) with `FiniteDimensional 𝕜 (E ⧸ E₀)`; $C$ is a `Submodule 𝕜 F` with `FiniteDimensional 𝕜 C`. The map $(x,c)\mapsto v(x)+c$ is `(v.comp E₀.subtypeL).coprod C.subtypeL : E₀ × C →L[𝕜] F`, and only its bijectivity as a function is assumed. Fredholm is Mathlib's `ContinuousLinearMap.IsFredholm`, and `index` is `FredholmBanach.index` (kernel minus cokernel, the opposite of Bourbaki's sign).
-- source:
--   Auxiliary statement for N. Bourbaki, Théories spectrales, Chapitres III à V, Springer (2023), https://doi.org/10.1007/978-3-031-19505-1, Chapitre III, § 4, n° 2, Théorème 1, p. TS III.58

import Definitions.Def_FredholmBanach_Setting

namespace FredholmBanach

/-- Let `E₀ ⊆ E` have finite codimension and `C ⊆ F` be finite-dimensional. If
`(x, c) ↦ v x + c` is a bijection `E₀ × C → F`, then `v` is Fredholm and
`index v = dim (E ⧸ E₀) - dim C`. -/
theorem isFredholm_index_of_bijective_coprod {𝕜 E F : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
    (E₀ : Submodule 𝕜 E) [FiniteDimensional 𝕜 (E ⧸ E₀)] (C : Submodule 𝕜 F) [FiniteDimensional 𝕜 C]
    (v : E →L[𝕜] F) (hv : Function.Bijective ((v.comp E₀.subtypeL).coprod C.subtypeL)) :
    v.IsFredholm ∧ index v =
      (Module.finrank 𝕜 (E ⧸ E₀) : ℤ) - (Module.finrank 𝕜 C : ℤ) := by sorry

end FredholmBanach
