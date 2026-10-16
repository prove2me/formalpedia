-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_CanonicalEmptyLayerGeometry_poly_mem
-- name    : OAI.Erdos3.VectorPolynomial.CanonicalEmptyLayerGeometry.poly_mem
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-16T01:37:31.823157+00:00
-- url     : https://prove2.me/theorems/6daf8a21-6ec4-4b1c-a20a-981368e8788e
-- title:
--   In the empty layer geometry every coefficient of the zero polynomial lies in U
-- statement:
--   For every natural number $q$, every type $X$, every $j \in \mathrm{Fin}\,q$ and every exponent vector $\alpha : X \to_0 \mathbb N$, the $\alpha$-coefficient of `CanonicalEmptyLayerGeometry.poly q X j` lies in `CanonicalEmptyLayerGeometry.U q j`. Here `poly q X j` is the zero vector-valued polynomial in `VectorPolynomial X ℝ (J q j → ℝ)` (that is, $\mathbb R[X] \otimes_{\mathbb R} \mathbb R^{J_{q,j}}$), `coefficients` is OpenAI's linear equivalence sending such a polynomial to its finitely supported family of vector coefficients indexed by monomial exponents, the coordinate type $J_{q,j}$ is empty, and `U q j` is the zero subspace $\bot$ of $\mathbb R^{J_{q,j}}$.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.CanonicalEmptyLayerGeometry.poly_mem` in `lean/OAI/Combinatorics/Progressions/Estimates/CanonicalEmptyLayerGeometry.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B1324` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/CanonicalEmptyLayerGeometry.lean#L737

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B1324

namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators Classical

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators Classical

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3

open scoped BigOperators Classical

namespace BooleanCubeKernel

end BooleanCubeKernel
end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

namespace BooleanCubeKernel

end BooleanCubeKernel
end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical

variable {G X : Type*} {I J : Fin 0 → Type*} {n : Fin 0 → ℕ}
    (B : LayerSamplerAxis I n → Type*)

variable [Fintype G] [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    [∀ a, Fintype (B a)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin 0 → ℝ}

variable (S : LayerSamplerScale (G := G) B U b R σ)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I J : Fin m → Type*} {n : Fin m → ℕ}
    [∀ j, IsEmpty (I j)] [∀ j, IsEmpty (Fin (n j))]
    (B : LayerSamplerAxis I n → Type*)

variable [Fintype G] [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    [∀ a, Fintype (B a)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ}

variable (S : LayerSamplerScale (G := G) B U b R σ)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators Classical

variable {G X : Type*} [Fintype G]
    {I J : Fin 0 → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin 0 → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin 0 → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial.CanonicalEmptyLayerGeometry

open Module Submodule

theorem poly_mem (q : ℕ) (X : Type*) (j : Fin q) (α : X →₀ ℕ) :
    coefficients (poly q X j) α ∈ U q j := by
  sorry

end Erdos3.VectorPolynomial.CanonicalEmptyLayerGeometry
end
end OAI
