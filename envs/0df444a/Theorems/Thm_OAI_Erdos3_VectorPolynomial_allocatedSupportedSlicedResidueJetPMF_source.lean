-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedSupportedSlicedResidueJetPMF_source
-- name    : OAI.Erdos3.VectorPolynomial.allocatedSupportedSlicedResidueJetPMF_source
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T16:37:20.571138+00:00
-- url     : https://prove2.me/theorems/f229a5d4-cec1-4395-93d2-6f47f7126f29
-- title:
--   The allocated supported sliced residue-jet PMF as an image of a product source
-- statement:
--   Let $m\in\mathbb N$, $G$ a finite type, $I\colon\mathrm{Fin}\,m\to$ Type a family of finite types with decidable equality, $n\colon\mathrm{Fin}\,m\to\mathbb N$, $B$ a family of finite types with decidable equality indexed by `LayerSamplerAxis I n` $=\Sigma_j\,I_j\oplus\mathrm{Fin}\,n_j$, $J\colon\mathrm{Fin}\,m\to$ Type finite types, $U_j$ a subspace of $\mathbb R^{J_j}$, `basis` $j$ a basis indexed by $\mathrm{Fin}\,n_j$ of the orthogonal complement of `euclideanSubspace (U j)`, $R,\sigma\colon\mathrm{Fin}\,m\to\mathbb R$ with $R_j>0$ and $\sigma_j>0$ (`hR`, `hσ`), and $S$ a `LayerSamplerScale B U basis R σ` (a structure bundling a positive natural number `S.value` with width and gap conditions). Let $\alpha$ be a finite type with decidable equality and $q>0$ (`hq`); write $\mathcal T=$ `PrincipalTupleIndex B (layerSamplerDegree I n)` (triples $\langle a,b,v\rangle$ with $b\in B(a)$ and $v<j+1$ for $a=\langle j,\_\rangle$). Let $r\colon\mathcal T\to\mathrm{Option}\,\alpha\to\mathbb Z/q$, $H,\mathrm{step}\colon\mathcal T\to\mathbb N$ with $H_t>0$ (`hH`) and $c\colon\mathcal T\to\mathbb Z$, with `integerProgressionSupport (c t) (step t) (H t)` $=\{c_t+\mathrm{step}_t\,i:0\le i<H_t\}\subseteq[0,\ $`allocatedPrincipalSides B U basis S t`$)$ for all $t$ (`hsubset`), and assume (`hcell`) that the event `principalResidueLabel q y = r` has positive mass under `principalTupleWeights B (layerSamplerDegree I n) H hH`. Fix $j\in\mathrm{Fin}\,m$ and $i\in\mathrm{Fin}\,n_j$, write $a_0=\langle j,\mathrm{inr}\,i\rangle$, and assume $\texttt{S.value}^{j+1}<$ `basisAxisScale (basis j) i` (`hactive`) and $(|\alpha|+1)\,q\le H_{\langle a_0,b,v\rangle}$ for all $b,v$ (`hsize`). Let `rows` be a `Finset (Finset α)` and `shift` an integer for each element of `rows`. Let `sources` $=$ `principalSupportedAxisSources B (layerSamplerDegree I n) H hH q hq r a₀ hsize` (for each $b\in B(a_0)$ and $v<j+1$ a `NormalizedScalarCubeSource α`, OpenAI's `normalizedUniformCubeSource` with side $H_{\langle a_0,b,v\rangle}$, modulus $q$ and residue $r_{\langle a_0,b,v\rangle}$); let `coeff` be the constant family $b\mapsto$ `allocatedPrincipalNormalizedSource B U basis hR S j i hactive` (a `NormalizedScalarCubeSource Empty`); let $\mathrm{lower}(b,v,a)=c_{\langle a_0,b,v\rangle}$ if $a=\mathrm{none}$ and $0$ otherwise; and let $\mathrm{strides}(b,v,a)=\mathrm{step}_{\langle a_0,b,v\rangle}$. Then the image of the PMF of `weightedModerateIntegerProductSource coeff sources` (product weights over $b\in B(a_0)$) under the map `weightedAffineModerateIntegerJetSum coeff sources lower strides rows (fun _ => 0) shift` (which adds to `shift` a sum over $b$ of `weightedAffineModerateIntegerBlock` terms) equals `allocatedSupportedSlicedResidueJetPMF B U basis hR hσ S q r H step c hH hsubset hcell j i rows shift`, the PMF on integer vectors indexed by `rows` obtained by drawing coefficients from the dependent product of `allocatedLayerIntegerPMFs B U basis hR hσ S j i` over the `principalCoefficientSlot`s of $b\in B(a_0)$, drawing $y$ from `containedSupportedProgressionLaw B (layerSamplerDegree I n) (allocatedPrincipalSides B U basis S) H step c … hH hsubset q r hcell`, and returning $\mathrm{shift}+\sum_b\mathrm{coeff}_b\cdot$ `integerBooleanBlockJet` of the coordinates of $y$ at $\langle a_0,b,\cdot\rangle$.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.allocatedSupportedSlicedResidueJetPMF_source` in `lean/OAI/Combinatorics/Progressions/Lattices/AllocatedSupportedSlicedResidueJet.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B145` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Lattices/AllocatedSupportedSlicedResidueJet.lean#L42

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B145

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (q : ℕ) (hq : 0 < q) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ t, 0 < H t)
variable (hsubset : ∀ t, integerProgressionSupport (c t) (step t : ℤ) (H t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ))
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n) H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
variable (j : Fin m) (i : Fin (n j))

local notation "conditioned" => containedSupportedProgressionLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) H step c (allocatedPrincipalSides_pos B U basis S) hH hsubset q r hcell

theorem allocatedSupportedSlicedResidueJetPMF_source
    (hactive : S.value ^ (j.val + 1) < basisAxisScale (basis j) i)
    (hsize : ∀ b v, (Fintype.card α + 1) * q ≤ H ⟨⟨j,Sum.inr i⟩,b,v⟩)
    (rows : Finset (Finset α)) (shift : rows → ℤ) :
    let sources := principalSupportedAxisSources B (layerSamplerDegree I n) H hH q hq r
      ⟨j, Sum.inr i⟩ hsize
    let coeff := fun _ : B ⟨j,Sum.inr i⟩ => allocatedPrincipalNormalizedSource B U basis hR S j i hactive
    let lower := fun (b : B ⟨j,Sum.inr i⟩) (v : Fin (j.val + 1)) (a : Option α) =>
      if a = none then c ⟨⟨j,Sum.inr i⟩,b,v⟩ else 0
    let strides := fun (b : B ⟨j,Sum.inr i⟩) (v : Fin (j.val + 1)) (_ : Option α) =>
      step ⟨⟨j,Sum.inr i⟩,b,v⟩
    (weightedModerateIntegerProductSource coeff sources).toPMF.map
      (weightedAffineModerateIntegerJetSum coeff sources lower strides rows (fun _ => 0) shift) =
      allocatedSupportedSlicedResidueJetPMF B U basis hR hσ S q r H step c hH hsubset hcell j i rows shift := by
  sorry

end Erdos3.VectorPolynomial
end
end OAI
