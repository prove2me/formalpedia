-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedFiberActiveProgression_common_contained
-- name    : OAI.Erdos3.VectorPolynomial.allocatedFiberActiveProgression_common_contained
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T16:50:57.578449+00:00
-- url     : https://prove2.me/theorems/dc0b5bc8-80e7-4a66-aead-fbc2b94cf8b7
-- title:
--   Active-axis fiber progressions of an allocated residue slice lie in [0, S.value)
-- statement:
--   The statement uses these section variables (including, through an `include`, the hypotheses $hlen$, $hfixed$, $hactive$). Let $m \in \mathbb{N}$, $G$ a finite type, $I_j, J_j$ ($j \in \mathrm{Fin}\ m$) finite types, $n : \mathrm{Fin}\ m \to \mathbb{N}$, $B_a$ finite types indexed by $a \in$ `LayerSamplerAxis I n` $= \Sigma_j\, I_j \oplus \mathrm{Fin}(n_j)$, $U_j \subseteq \mathbb{R}^{J_j}$ real subspaces, $\mathrm{basis}_j$ a real basis of the orthogonal complement of `euclideanSubspace (U j)` indexed by $\mathrm{Fin}(n_j)$, $R, \sigma : \mathrm{Fin}\ m \to \mathbb{R}$, and $S$ a `LayerSamplerScale B U basis R σ` (OpenAI's structure: a positive natural number $S.\mathrm{value}$ with width and gap conditions). Write $\deg$ = `layerSamplerDegree I n` ($\deg(j, \cdot) = j + 1$), $\mathrm{Input}$ = `PrincipalTupleIndex B deg` $= \Sigma_a\, B_a \times \mathrm{Fin}(\deg a)$, and call an axis $a$ short if `allocatedShortAxis U basis S.value a` (OpenAI's predicate on axes) and active otherwise. Let $\mathrm{keep}$ be a decidable predicate on $G \oplus \mathrm{Input}$, $q \in \mathbb{N}$, and $\mathrm{slice}$ a `ResidueBoxSlice` of step $q$ on the kept indices for the side lengths $S.\mathrm{value}$ on $G$ and `allocatedPrincipalSides B U basis S` on $\mathrm{Input}$ (start points and lengths with $\mathrm{start}_k + qj$ below the side length for $j < \mathrm{length}_k$). Assume every slice length is positive; let $\mathrm{fixed}$ assign to each non-kept index $k$ an integer with $0 \le \mathrm{fixed}_k <$ its side length; and assume every index $\mathrm{inr}(a, b, t)$ with $a$ active is kept. Then for every index $j = (a, b, t)$ with $a$ active, the set `integerProgressionSupport (slice.fiberParameterStart fixed (inr j)) q (slice.fiberParameterLength (inr j))` $= \{\mathrm{start} + q k : 0 \le k < \mathrm{length}\}$ (with start and length those of the slice at $\mathrm{inr}(j)$ when that index is kept, and $\mathrm{fixed}$ and $1$ otherwise) is contained in the integer interval $[0, S.\mathrm{value})$.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.allocatedFiberActiveProgression_common_contained` in `lean/OAI/Combinatorics/Progressions/Estimates/ActualFiberSlicedBoundedTwistPrecision.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B135`, `OAIErdos3B141` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/ActualFiberSlicedBoundedTwistPrecision.lean#L46

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B135
import Definitions.Def_OAIErdos3B141

namespace OAI

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "degree" => layerSamplerDegree I n
local notation "sides" => allocatedPrincipalSides B U basis S
local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "Input" => PrincipalTupleIndex B degree
local notation "ActiveInput" => PrincipalTupleIndex (fun a : Active => B (Subtype.val a))
  (fun a : Active => degree (Subtype.val a))

variable {keep : G ⊕ PrincipalTupleIndex B (layerSamplerDegree I n) → Prop} [DecidablePred keep]
variable {q : ℕ}
variable (slice : ResidueBoxSlice
  (fun k : {k // keep k} => Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U basis S) k.val) q)
variable (hlen : ∀ k, 0 < slice.length k) (fixed : {k // ¬keep k} → ℤ)
variable (hfixed : ∀ k, 0 ≤ fixed k ∧
  fixed k < ((Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U basis S) k.val : ℕ) : ℤ))
variable (hkernel : ∀ g, keep (Sum.inl g))

variable (hactive : ∀ j : PrincipalTupleIndex
  (fun a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U basis S.value a} => B a.val)
  (fun a => layerSamplerDegree I n a.val), keep (Sum.inr ⟨j.1.val, j.2⟩))

include hlen hfixed hactive in
theorem allocatedFiberActiveProgression_common_contained (j : ActiveInput) :
    integerProgressionSupport (slice.fiberParameterStart fixed (Sum.inr ⟨j.1.val, j.2⟩))
      (q : ℤ) (slice.fiberParameterLength (Sum.inr ⟨j.1.val, j.2⟩)) ⊆
        Finset.Ico (0 : ℤ) (S.value : ℤ) := by
  sorry

end Erdos3.VectorPolynomial
end
end OAI
