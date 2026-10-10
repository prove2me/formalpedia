-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedFixedPath_sliced_principal_geometry
-- name    : OAI.Erdos3.VectorPolynomial.allocatedFixedPath_sliced_principal_geometry
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-09T16:52:18.660554+00:00
-- url     : https://prove2.me/theorems/865f96a8-0ad2-4b5a-bcc3-3792244b3d91
-- title:
--   Normalized lower ends and widths of fixed-path sliced progressions
-- statement:
--   Let $m\in\mathbb N$, $G$ a finite type, $I,J\colon\mathrm{Fin}\,m\to$ Type families of finite types, $n\colon\mathrm{Fin}\,m\to\mathbb N$, $B$ a family of finite types indexed by `LayerSamplerAxis I n` $=\Sigma_j\,I_j\oplus\mathrm{Fin}\,n_j$, $U_j$ a subspace of $\mathbb R^{J_j}$, `basis` $j$ a basis indexed by $\mathrm{Fin}\,n_j$ of the orthogonal complement of `euclideanSubspace (U j)` (the subspace $U_j$ viewed in Euclidean space), $R,\sigma\colon\mathrm{Fin}\,m\to\mathbb R$, and $S$ a `LayerSamplerScale B U basis R σ` (a structure bundling a positive natural number `S.value` with width and gap conditions). Call an axis $a$ active if not `allocatedShortAxis U basis S.value a` (an axis $\langle j,\mathrm{inr}\,i\rangle$ is short when `basisAxisScale (basis j) i` $=\lceil\|\mathrm{basis}_j(i)\|^{-1}\rceil\le\texttt{S.value}^{j+1}$; axes $\langle j,\mathrm{inl}\,\_\rangle$ are never short), and let the inputs be the triples $\langle a,b,k\rangle$ with $a$ active, $b\in B(a)$ and $k\in\mathrm{Fin}$ (`layerSamplerDegree I n a`), where `layerSamplerDegree I n ⟨j, _⟩` $=j+1$. Let $g$ (`stepG`) be a positive natural number, $H$ a natural number and $c$ an integer for each input, with $H_x\ge2$ for all inputs $x$, and $\delta>0$. Assume that for every input $x$ the set `integerProgressionSupport (c x) g (H x)` $=\{c_x+gi:0\le i<H_x\}$ is contained in $[0,\texttt{S.value})$ and has at least $\delta\cdot\texttt{S.value}$ elements. Put $\mathrm{lower}(x)=c_x/\texttt{S.value}$ and $\mathrm{width}(x)=g(H_x-1)/\texttt{S.value}$. Then for every input $x$: $\delta/2\le\mathrm{width}(x)$, $0\le\mathrm{lower}(x)$, and $|\mathrm{lower}(x)|+|\mathrm{width}(x)|\le1$.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.allocatedFixedPath_sliced_principal_geometry` in `lean/OAI/Combinatorics/Progressions/Dynamics/AllocatedFixedPathSlicedNativeAmbientComparison.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B141` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Dynamics/AllocatedFixedPathSlicedNativeAmbientComparison.lean#L45

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B141

namespace OAI

section

namespace Erdos3

namespace VectorPolynomial

open scoped Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "Active" => {a : LayerSamplerAxis I n //
  ¬allocatedShortAxis (I := I) U basis S.value a}
local notation "Input" => (Σ a : Active, B (Subtype.val a) × Fin (layerSamplerDegree I n (Subtype.val a)))

theorem allocatedFixedPath_sliced_principal_geometry
    (stepG : ℕ) (hstepG : 0 < stepG) (H : Input → ℕ) (c : Input → ℤ)
    (hH : ∀ j, 2 ≤ H j) {δ : ℝ} (hδ : 0 < δ)
    (hsubset : ∀ j, integerProgressionSupport (c j) (stepG : ℤ) (H j) ⊆
      Finset.Ico (0 : ℤ) (S.value : ℤ))
    (hdense : ∀ j, δ * S.value ≤
      ((integerProgressionSupport (c j) (stepG : ℤ) (H j)).card : ℝ)) :
    let lower := fun (a : Active) (p : B a.val × Fin (layerSamplerDegree I n a.val)) =>
      (c ⟨a, p⟩ : ℝ) / S.value
    let width := fun (a : Active) (p : B a.val × Fin (layerSamplerDegree I n a.val)) =>
      (stepG : ℝ) * ((H ⟨a, p⟩ : ℝ) - 1) / S.value
    (∀ a p, δ / 2 ≤ width a p) ∧ (∀ a p, 0 ≤ lower a p) ∧
      (∀ a p, |lower a p| + |width a p| ≤ 1) := by
  sorry

end VectorPolynomial
end Erdos3
end
end OAI
