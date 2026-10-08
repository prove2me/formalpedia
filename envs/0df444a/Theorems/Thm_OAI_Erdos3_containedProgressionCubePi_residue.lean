-- Prove2me | Theorems.Thm_OAI_Erdos3_containedProgressionCubePi_residue
-- name    : OAI.Erdos3.containedProgressionCubePi_residue
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T11:04:33.827567+00:00
-- url     : https://prove2.me/theorems/6da324e1-e968-4a77-8917-3881abd93af0
-- title:
--   On the support, the contained-progression cube map is c + step·x modulo q
-- statement:
--   Let $G$ be a finite type, $L>0$ a natural number, $H,\mathrm{step} : G\to\mathbb{N}$ with $H_g>0$ for every $g$, and $c : G\to\mathbb{Z}$. Assume that for every $g$, `integerProgressionSupport (c g) (step g) (H g)` (the set $\{c_g+\mathrm{step}_g\,t : t\in\mathbb{Z},\ 0\le t<H_g\}$) is contained in $\{0,1,\dots,L-1\}$. Let $x$ assign to each $g$ an element $x_g$ of `IntegerScalarCubeBox Empty (H g)` (a function from $\mathrm{Option}\ \mathrm{Empty}$ to the integers in $[-H_g,H_g)$), and assume $x$ has nonzero weight under the product (`FiniteProbabilityWeights.pi`) of the probability weights `integerScalarCubeWeights Empty (H g)` (OpenAI's uniform distribution on the integer scalar cubes of size $H_g$, i.e. on the $y$ in the box with $y_{\mathrm{none}}+\sum_{i\in t}y_{\mathrm{some}\ i}\in[0,H_g)$ for all $t$). Let $q$ be a natural number. Then, as functions $G\to\mathbb{Z}/q$, the residue modulo $q$ of the $\mathrm{none}$-coordinate of `containedProgressionCubeMap Empty L (H g) (step g) (c g) hL (hsubset g) (x g)` (OpenAI's map that sends an integer scalar cube $z$ of size $H_g$ to $i\mapsto[i=\mathrm{none}]\,c_g+\mathrm{step}_g\,z_i$, and anything else to $0$) equals $g\mapsto (c_g+\mathrm{step}_g\cdot x_g(\mathrm{none}))\bmod q$.
--
--   Lean: `OAI.Erdos3.containedProgressionCubePi_residue` in `lean/OAI/Combinatorics/Progressions/Lattices/AllocatedSlicedPhysicalResidueIdentity.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B012` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Lattices/AllocatedSlicedPhysicalResidueIdentity.lean#L11

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B012

namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

theorem containedProgressionCubePi_residue
    {G : Type*} [Fintype G] (L : ℕ) (hL : 0 < L)
    (H step : G → ℕ) (c : G → ℤ) (hH : ∀ g, 0 < H g)
    (hsubset : ∀ g, integerProgressionSupport (c g) (step g : ℤ) (H g) ⊆
      Finset.Ico (0 : ℤ) (L : ℤ))
    (x : ∀ g, IntegerScalarCubeBox Empty (H g))
    (hx : (FiniteProbabilityWeights.pi
      (fun g => integerScalarCubeWeights Empty (H g) (hH g))).weight x ≠ 0)
    (q : ℕ) :
    (fun g => ((containedProgressionCubeMap Empty L (H g) (step g) (c g)
      hL (hsubset g) (x g) none : ℤ) : ZMod q)) =
      fun g => ((c g + (step g : ℤ) * (x g none : ℤ) : ℤ) : ZMod q) := by
  sorry

end Erdos3
end
end OAI
