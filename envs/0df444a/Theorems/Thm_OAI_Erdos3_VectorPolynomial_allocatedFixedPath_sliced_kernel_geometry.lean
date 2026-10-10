-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedFixedPath_sliced_kernel_geometry
-- name    : OAI.Erdos3.VectorPolynomial.allocatedFixedPath_sliced_kernel_geometry
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-10T01:25:31.93187+00:00
-- url     : https://prove2.me/theorems/a033506f-7635-4226-b75b-b000bd481962
-- title:
--   Contained kernel progressions give normalized lower ends and widths inside [0, 1]
-- statement:
--   Fix the section data: a natural number $m$; finite types $G$ and $I_j$, natural numbers $n_j$, finite types $B_a$ over the axes $a$ of `LayerSamplerAxis I n`, finite types $J_j$, real subspaces $U_j \subseteq \mathbb R^{J_j}$, bases `basis j` (indexed by $\mathrm{Fin}\,n_j$) of the orthogonal complements of `euclideanSubspace (U j)`, real functions $R, \sigma$ on $\mathrm{Fin}\,m$, and a layer-sampler scale `S : LayerSamplerScale B U basis R σ` (a structure bundling a positive natural number $L = $ `S.value` with width and gap inequalities). Let $H_G : G \to \mathbb N$ with $2 \le H_G(g)$ for all $g$, let $c_G : G \to \mathbb Z$, and let $\mathrm{step}_G$ be a positive natural number such that for every $g$ the progression $\{c_G(g) + \mathrm{step}_G\,k : 0 \le k < H_G(g)\}$ (`integerProgressionSupport`) is contained in $[0, L) \cap \mathbb Z$. Then for every $g \in G$: $0 \le c_G(g)/L$; $0 \le \mathrm{step}_G\,(H_G(g) - 1)/L$; $c_G(g)/L + \mathrm{step}_G\,(H_G(g)-1)/L \le 1$; and $0 < \mathrm{step}_G\,(H_G(g) - 1)/L$ (with $H_G(g) - 1$ computed in $\mathbb N$).
--
--   Lean: `OAI.Erdos3.VectorPolynomial.allocatedFixedPath_sliced_kernel_geometry` in `lean/OAI/Combinatorics/Progressions/Dynamics/AllocatedFixedPathSlicedNativeAmbientComparison.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B152` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Dynamics/AllocatedFixedPathSlicedNativeAmbientComparison.lean#L24

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B152

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

theorem allocatedFixedPath_sliced_kernel_geometry
    (HG : G → ℕ) (hHG : ∀ g, 2 ≤ HG g) (cG : G → ℤ)
    (stepG : ℕ) (hstepG : 0 < stepG)
    (hcontainedG : ∀ g, integerProgressionSupport (cG g) (stepG : ℤ) (HG g) ⊆
      Finset.Ico (0 : ℤ) (S.value : ℤ)) :
    (∀ g, 0 ≤ (cG g : ℝ) / S.value) ∧
    (∀ g, 0 ≤ (stepG : ℝ) * ((HG g - 1 : ℕ) : ℝ) / S.value) ∧
    (∀ g, (cG g : ℝ) / S.value +
      (stepG : ℝ) * ((HG g - 1 : ℕ) : ℝ) / S.value ≤ 1) ∧
    (∀ g, 0 < (stepG : ℝ) * ((HG g - 1 : ℕ) : ℝ) / S.value) := by
  sorry

end VectorPolynomial
end Erdos3
end
end OAI
