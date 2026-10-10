-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedActiveContainedProgression_residue_join
-- name    : OAI.Erdos3.VectorPolynomial.allocatedActiveContainedProgression_residue_join
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-10T05:48:39.319052+00:00
-- url     : https://prove2.me/theorems/99de21fa-ec2d-4f39-b3b5-5afa5c954d08
-- title:
--   Residues of the joined active contained progression are the progression residues
-- statement:
--   Fix the section data: a natural number $m$; a finite type $G$; finite types $I_j$ and natural numbers $n_j$ ($j \in \mathrm{Fin}\,m$); finite types $B_a$ over the axes $a$ of `LayerSamplerAxis I n` (the sigma type $\Sigma_j\, I_j \oplus \mathrm{Fin}(n_j)$); finite types $J_j$, real subspaces $U_j \subseteq \mathbb R^{J_j}$ and bases `basis j` (indexed by $\mathrm{Fin}\,n_j$) of the orthogonal complements of `euclideanSubspace (U j)`; real functions $R, \sigma$ on $\mathrm{Fin}\,m$; and a `LayerSamplerScale` $S$ (a structure bundling a positive natural number $S.\mathrm{value}$ with width and gap inequalities). Let short be the predicate `allocatedShortAxis U basis S.value` on axes, Active the non-short axes, degree $=$ `layerSamplerDegree I n` ($a \mapsto j+1$ on layer $j$), Input $= \Sigma_{a \in \mathrm{Active}}\, B_a \times \mathrm{Fin}(\mathrm{degree}(a))$, and sides $=$ `allocatedPrincipalSides B U basis S`.
--
--   Let $\mathrm{step}, H : \mathrm{Input} \to \mathbb N$ and $c : \mathrm{Input} \to \mathbb Z$ with $H_j > 0$ for all $j$, and assume (hsubset) that for every $j$ the progression `integerProgressionSupport (c j) (step j) (H j)` $= \{c_j + \mathrm{step}_j k : 0 \le k < H_j\}$ is contained in $[0, S.\mathrm{value})$. Let $v$ assign to each $j$ a point $v_j$ of `IntegerScalarCubeBox Empty (H j)` (a map $\mathrm{Option}\,\mathrm{Empty} \to [-H_j, H_j) \cap \mathbb Z$), with nonzero weight under the product over $j$ of the weights `integerScalarCubeWeights Empty (H j)` (finite probability weights on the box). Let $q \in \mathbb N$ and $u$ in `PrincipalAxisTuples short sides` (with $\alpha = \mathrm{Empty}$; the integer tuples on the short axes). Then
--   `principalResidueLabel q (principalAxisJoin short u (allocatedActiveContainedProgression B U basis S step H c hsubset v))`
--   (the coordinatewise reduction mod $q$ of the full tuple that agrees with $u$ on short axes and with the image of $v$ under `containedProgressionCubeMap` on active axes) equals
--   `allocatedPrincipalResidueJoin B U basis S q u (j ↦ c j + step j * v j none mod q)`
--   (the residue tuple equal to $u \bmod q$ on short axes and to $c_j + \mathrm{step}_j\, v_j(\mathrm{none}) \bmod q$ at each active index $j$).
--
--   Lean: `OAI.Erdos3.VectorPolynomial.allocatedActiveContainedProgression_residue_join` in `lean/OAI/Combinatorics/Progressions/Lattices/AllocatedSlicedPhysicalResidueIdentity.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B171`, `OAIErdos3B178` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Lattices/AllocatedSlicedPhysicalResidueIdentity.lean#L48

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B171
import Definitions.Def_OAIErdos3B178

namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

namespace VectorPolynomial

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "degree" => layerSamplerDegree I n
local notation "Input" => (Σ a : Active, B (Subtype.val a) × Fin (degree (Subtype.val a)))
local notation "sides" => allocatedPrincipalSides B U basis S

theorem allocatedActiveContainedProgression_residue_join
    (step H : Input → ℕ) (c : Input → ℤ) (hH : ∀ j, 0 < H j)
    (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
      Finset.Ico (0 : ℤ) (S.value : ℤ))
    (v : ∀ j, IntegerScalarCubeBox Empty (H j))
    (hv : (FiniteProbabilityWeights.pi
      (fun j => integerScalarCubeWeights Empty (H j) (hH j))).weight v ≠ 0)
    (q : ℕ) (u : PrincipalAxisTuples (α := Empty) short sides) :
    principalResidueLabel q (principalAxisJoin short u
      (allocatedActiveContainedProgression B U basis S step H c hsubset v)) =
      allocatedPrincipalResidueJoin B U basis S q u
        (fun j => ((c j + (step j : ℤ) * (v j none : ℤ) : ℤ) : ZMod q)) := by
  sorry

end VectorPolynomial
end Erdos3
end
end OAI
