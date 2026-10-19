-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedFiberSliceLaw_sliced_source_complexMean_s2
-- name    : OAI.Erdos3.VectorPolynomial.allocatedFiberSliceLaw_sliced_source_complexMean_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T04:57:22.966988+00:00
-- url     : https://prove2.me/theorems/99f8e3e8-c2e7-4b37-a885-cac72f0e6209
-- title:
--   The fiber slice law mean factors as an inactive-interval mean of a kernel mean of an active-progression mean
-- statement:
--   **Setup.** Fix the data of OpenAI's allocated layer-sampler setup: a natural number $m$; finite types $G$ (with decidable equality), $I_j$ (with decidable equality) and $J_j$ for $j < m$, and $B(a)$ for each layer-sampler axis $a$ (finite, with decidable equality); dimensions $n_j$; subspaces $U_j \subseteq \mathbb{R}^{J_j}$; bases `basis j` (indexed by $\{0,\dots,n_j-1\}$) of the orthogonal complement of $U_j$; reals $R_j, \sigma_j$; and a `LayerSamplerScale B U basis R σ` $S$, with positive integer side `S.value`. Write `sides` $=$ `allocatedPrincipalSides B U basis S` (a side length for each principal tuple index), `short` $=$ `allocatedShortAxis U basis S.value` (a predicate on axes; the other axes are called active), $\mathrm{Input}$ = `PrincipalTupleIndex B (layerSamplerDegree I n)` and $\mathrm{ActiveInput}$ the principal tuple index of the active axes.
--
--   Let `keep` be a decidable predicate on $G \sqcup \mathrm{Input}$ with ($hkernel$) `keep` true on every element of $G$. Let $q$ be a natural number and `slice` a `ResidueBoxSlice` with modulus $q$ for the box whose side at a kept coordinate $k$ is `S.value` if $k \in G$ and `sides k` if $k \in \mathrm{Input}$ (an OpenAI structure: for each kept coordinate $k$ a start $a_k$ and a length $\ell_k$ with $a_k + q j$ less than the side for all $j < \ell_k$). Assume ($hlen$) $\ell_k > 0$ for every kept $k$, and let `fixed` assign to each non-kept coordinate $k$ an integer with ($hfixed$) $0 \le \texttt{fixed}(k) <$ the side at $k$.
--
--   Let $\varphi$ be any function from pairs (an element of $G \to$ `IntegerScalarCubeBox Empty S.value`, an element of `PrincipalIntegerTuples B degree Empty sides`) to $\mathbb{C}$. Define, for $j \in \mathrm{Input}$: $H(j)$ = `slice.fiberParameterLength (inr j)` (the slice length $\ell_j$ if $j$ is kept, else $1$); $\mathrm{step}(j)$ = `fiberParameterStride (inr j)` ($q$ if $j$ is kept, else $0$); $\mathrm{start}(j)$ = `slice.fiberParameterStart fixed (inr j)` ($a_j$ if kept, else $\texttt{fixed}(j)$). Let $H_{\mathrm{active}}$ and $\mathrm{step}_{\mathrm{active}}$ be the restrictions of $H$ and $\mathrm{step}$ to the active axes (`principalAxisLength (¬short)`), and $c_{\mathrm{active}}$ the restriction of $\mathrm{start}$ to $\mathrm{ActiveInput}$. Let `kernel` be the product over $g \in G$ of the probability weights `integerScalarCubeWeights Empty ℓ_g`, `active` the product over $j \in \mathrm{ActiveInput}$ of `integerScalarCubeWeights Empty (H_active j)`, and let `embed x` send $x = (x_g)_{g \in G}$ to $(g \mapsto \texttt{containedProgressionCubeMap Empty S.value}\ \ell_g\ q\ a_g\ (x_g))$, which maps the cube of side $\ell_g$ onto the progression $a_g + q\cdot\{0,\dots,\ell_g - 1\}$ inside the box of side `S.value`.
--
--   Then
--   $$\texttt{(slice.fiberSliceLaw hlen fixed hfixed).complexMean}\bigl(z \mapsto \varphi(\texttt{kernelZeroTupleFromSumIntegerBox}\ z,\ \texttt{principalZeroTupleFromSumIntegerBox}\ z)\bigr)$$
--   equals
--   $$\texttt{(allocatedInactiveAffineIntervalLaw B U basis S H step start inside pos).complexMean}\Bigl(u \mapsto \texttt{kernel.complexMean}\bigl(x \mapsto \texttt{active.complexMean}(v \mapsto \varphi(\texttt{embed}\ x,\ \texttt{principalAxisJoin short}\ u\ w_v))\bigr)\Bigr),$$
--   where $w_v$ = `allocatedActiveContainedProgression B U basis S step_active H_active c_active hsubset v` (OpenAI: the active-axis tuple obtained by placing each cube coordinate of $v$ on the corresponding progression). Here `fiberSliceLaw` is the uniform law on the slice points (fixed coordinates set to `fixed`), `complexMean` is the weighted average $\sum_x w(x) f(x)$, and `allocatedInactiveAffineIntervalLaw` is OpenAI's law on the short-axis tuples given by the arithmetic progressions $\mathrm{start}(j) + \mathrm{step}(j)\cdot\{0,\dots,H(j)-1\}$; `kernelZeroTupleFromSumIntegerBox` and `principalZeroTupleFromSumIntegerBox` split a point of the full integer box into its $G$-part and its principal-tuple part. The arguments `inside`, `pos` and `hsubset` are the containment and positivity facts OpenAI derives from $hlen$ and $hfixed$.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.allocatedFiberSliceLaw_sliced_source_complexMean_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.allocatedFiberSliceLaw_sliced_source_complexMean` (in `lean/OAI/Combinatorics/Progressions/Probability/AllocatedFiberSlicedSourceLaw.lean`); the definitions it uses are in the definitions bundles `OAIE3v2B127`, `OAIE3v2B232`, `OAIE3v2B236` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Probability/AllocatedFiberSlicedSourceLaw.lean (declaration OAI.Erdos3.VectorPolynomial.allocatedFiberSliceLaw_sliced_source_complexMean)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B127
import Definitions.Def_OAIE3v2B232
import Definitions.Def_OAIE3v2B236

section

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
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

theorem allocatedFiberSliceLaw_sliced_source_complexMean_s2
    (φ : (G → IntegerScalarCubeBox Empty S.value) →
      PrincipalIntegerTuples B degree Empty sides → ℂ) :
    let H := fun j : Input => slice.fiberParameterLength (Sum.inr j)
    let step := fun j : Input => ResidueBoxSlice.fiberParameterStride (keep := keep) (q := q) (Sum.inr j)
    let start := fun j : Input => slice.fiberParameterStart fixed (Sum.inr j)
    let inside := slice.fiberPrincipalParameter_inside hlen fixed hfixed
    let pos := fun j : Input => slice.fiberParameterLength_pos hlen (Sum.inr j)
    let Hactive := principalAxisLength (fun a => ¬short a) H
    let stepActive := principalAxisLength (fun a => ¬short a) step
    let cActive := fun j : ActiveInput => start ⟨j.1.val, j.2⟩
    let hsubset := allocatedFiberActiveProgression_contained B U basis S slice hlen fixed hfixed
    let kernel := FiniteProbabilityWeights.pi (fun g => integerScalarCubeWeights Empty
      (slice.length ⟨Sum.inl g, hkernel g⟩) (hlen ⟨Sum.inl g, hkernel g⟩))
    let active := FiniteProbabilityWeights.pi (fun j : ActiveInput =>
      integerScalarCubeWeights Empty (Hactive j) (pos ⟨j.1.val, j.2⟩))
    let embed := fun (x : ∀ g, IntegerScalarCubeBox Empty (slice.length ⟨Sum.inl g, hkernel g⟩)) g =>
      containedProgressionCubeMap Empty S.value (slice.length ⟨Sum.inl g, hkernel g⟩)
        q (slice.start ⟨Sum.inl g, hkernel g⟩) S.positive
        (slice.fiberKernelProgression_contained hkernel g) (x g)
    (slice.fiberSliceLaw hlen fixed hfixed).complexMean (fun z =>
      φ (kernelZeroTupleFromSumIntegerBox B degree (fun _ : G => S.value) sides z)
        (principalZeroTupleFromSumIntegerBox B degree (fun _ : G => S.value) sides z)) =
      (allocatedInactiveAffineIntervalLaw B U basis S H step start inside pos).complexMean (fun u =>
        kernel.complexMean (fun x => active.complexMean (fun v =>
          φ (embed x) (principalAxisJoin short u
            (allocatedActiveContainedProgression B U basis S stepActive Hactive cActive hsubset v))))) := by
  sorry

end Erdos3.VectorPolynomial

end

end OAI
end
