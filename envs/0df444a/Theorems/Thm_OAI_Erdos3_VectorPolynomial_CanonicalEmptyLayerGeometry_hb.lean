-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_CanonicalEmptyLayerGeometry_hb
-- name    : OAI.Erdos3.VectorPolynomial.CanonicalEmptyLayerGeometry.hb
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-16T01:37:09.979973+00:00
-- url     : https://prove2.me/theorems/bc3005e2-1814-414d-89b5-38469a196192
-- title:
--   In the empty layer geometry the basis spans the projected integer lattice
-- statement:
--   For every natural number $q$ and every $j \in \mathrm{Fin}\,q$, the $\mathbb Z$-span of the range of `CanonicalEmptyLayerGeometry.b q j` equals `projectedIntegerLattice (euclideanSubspace (CanonicalEmptyLayerGeometry.U q j))`. Here, in OpenAI's `CanonicalEmptyLayerGeometry` construction, the coordinate type $J_{q,j}$ is empty, `U q j` is the zero subspace $\bot$ of $\mathbb R^{J_{q,j}}$, `euclideanSubspace` is the same subspace viewed inside the Euclidean space $\ell^2(J_{q,j})$, `b q j` is the empty basis (indexed by $\mathrm{Fin}\,0$) of its orthogonal complement, and `projectedIntegerLattice W` is the $\mathbb Z$-submodule of $W^\perp$ obtained as the image of the standard integer lattice in $W^\perp$ (`orthogonalLatticeImage`).
--
--   Lean: `OAI.Erdos3.VectorPolynomial.CanonicalEmptyLayerGeometry.hb` in `lean/OAI/Combinatorics/Progressions/Estimates/CanonicalEmptyLayerGeometry.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B1324` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/CanonicalEmptyLayerGeometry.lean#L714

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

theorem hb (q : ℕ) (j : Fin q) :
    span ℤ (Set.range (b q j)) = projectedIntegerLattice (euclideanSubspace (U q j)) := by
  sorry

end Erdos3.VectorPolynomial.CanonicalEmptyLayerGeometry
end
end OAI
