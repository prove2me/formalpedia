-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedSupportedSlicedInactiveResidueJetPMF_source_s2
-- name    : OAI.Erdos3.VectorPolynomial.allocatedSupportedSlicedInactiveResidueJetPMF_source_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T04:27:39.475802+00:00
-- url     : https://prove2.me/theorems/0dbbab11-bddc-418c-93e3-b9c8054bb5cc
-- title:
--   On a short inactive integer axis, the supported sliced residue jet law is the image of a product of uniform residue cube sources
-- statement:
--   Let $m$ be a natural number and $G$ a finite type. For each $j < m$ let $I_j$ (finite, with decidable equality) and $J_j$ (finite) be types, $n_j$ a natural number, $U_j$ a real subspace of $\mathbb{R}^{J_j}$ and $\mathrm{basis}_j$ a real basis, indexed by $\{0, \dots, n_j - 1\}$, of the orthogonal complement of the Euclidean subspace given by $U_j$. For each layer sampler axis $a$ (OpenAI's `LayerSamplerAxis I n`: pairs $(j, c)$ with $c \in I_j \sqcup \{0,\dots,n_j-1\}$; the axis $(j, c)$ has degree $j+1$) let $B_a$ be a finite type with decidable equality. Let $R, \sigma : \{0,\dots,m-1\} \to \mathbb{R}$ with $R_j, \sigma_j > 0$, and let $S$ be a layer sampler scale (OpenAI's `LayerSamplerScale B U basis R σ`, main field a positive natural number `S.value`). Let $\alpha$ be a finite type with decidable equality. The principal tuple indices are the triples $t = (a, b, v)$ with $a$ an axis, $b \in B_a$ and $v < \deg a$.
--
--   Let $q > 0$ be a natural number, $r$ a function assigning to each principal index $t$ and each element of $\mathrm{Option}\,\alpha$ a residue in $\mathbb{Z}/q\mathbb{Z}$, $H, \mathrm{step}$ natural-number functions and $c$ an integer function of the principal index, with $H_t > 0$ for all $t$. Assume that for every $t$ the progression $\{c_t + \mathrm{step}_t\, k : 0 \le k < H_t\}$ is contained in $\{0, \dots, \mathrm{side}_t - 1\}$, where $\mathrm{side}$ = `allocatedPrincipalSides B U basis S` (OpenAI side lengths), and that the residue cell $\{y : y_t(\cdot) \equiv r_t(\cdot) \pmod q\ \forall t\}$ has positive mass under `principalTupleWeights B (layerSamplerDegree I n) H hH` (OpenAI's product of integer scalar cube weights with lengths $H_t$). Fix $j < m$ and $i < n_j$, and write $a_0 = (j, i)$ for the integer axis. Assume:
--   - `basisAxisScale (basis j) i` $\le \texttt{S.value}^{\,j+1}$, where `basisAxisScale b i` $= \lceil 1/\lVert b_i \rVert \rceil$ (OpenAI);
--   - $2\cdot$`inactiveDenominator (principalProfileSize R_j k)` $\le$ `basisAxisScale (basis j) i`, where $k$ is the number of elements of OpenAI's `layerIntegerPrincipalSlots B j i`, `principalProfileSize R k` $= R/(8(k+1))$ and `inactiveDenominator γ` $= \max(1, \lceil 1/\gamma \rceil)$ (OpenAI);
--   - $(|\alpha| + 1)\,q \le H_{(a_0, b, v)}$ for all $b \in B_{a_0}$ and $v \le j$.
--
--   Let $\mathcal{R}$ be a finite set of finite subsets of $\alpha$ and $\mathrm{shift} : \mathcal{R} \to \mathbb{Z}$. For $b \in B_{a_0}$ and $v \le j$, let $\mathrm{src}_{b,v}$ = `principalSupportedAxisSources … a₀ … b v`, OpenAI's normalized uniform cube source of length $H_{(a_0,b,v)}$ with all moduli equal to $q$ and residues $r_{(a_0,b,v)}$ (its law is uniform on the points of the cube $\mathrm{Option}\,\alpha \to [-H, H) \cap \mathbb{Z}$ in OpenAI's residue support), let $\mathrm{lower}_{b,v}(\mathrm{none}) = c_{(a_0,b,v)}$ and $\mathrm{lower}_{b,v}(\alpha') = 0$ for $\alpha' \in \alpha$, and $\mathrm{stride}_{b,v} \equiv \mathrm{step}_{(a_0,b,v)}$. Then the image of the product law `weightedCubeIntegerSource src` (independent samples $x_{b,v}$ from the sources) under `affineWeightedCubeIntegerSum src lower stride 𝓡 shift`, the map
--   $$x \mapsto \Bigl(\mathrm{shift}(T) + \sum_{b \in B_{a_0}} \mathrm{jet}_T\bigl((\mathrm{lower}_{b,v} + \mathrm{stride}_{b,v}\, x_{b,v})_{v \le j}\bigr)\Bigr)_{T \in \mathcal{R}},$$
--   equals `allocatedSupportedSlicedResidueJetPMF B U basis hR hσ S q r H step c hH hsubset hcell j i 𝓡 shift`. Here $\mathrm{jet}_T(w) = \sum_{T' \subseteq T} (-1)^{|T \setminus T'|} \prod_{v} \bigl(w_v(\mathrm{none}) + \sum_{\alpha' \in T'} w_v(\alpha')\bigr)$ is OpenAI's `integerBooleanBlockJet`, and `allocatedSupportedSlicedResidueJetPMF` (OpenAI) is the law obtained by sampling, independently for each $b \in B_{a_0}$, an integer coefficient $\mathrm{coeff}_b$ from OpenAI's allocated layer integer law at the principal coefficient slot of $(a_0, b)$, then sampling $y$ from the contained supported progression law (OpenAI's `containedSupportedProgressionLaw` with sides `allocatedPrincipalSides B U basis S` and the data $H, \mathrm{step}, c, q, r$), and returning $\bigl(\mathrm{shift}(T) + \sum_{b} \mathrm{coeff}_b \cdot \mathrm{jet}_T((y_{(a_0,b,v)})_{v \le j})\bigr)_{T \in \mathcal{R}}$.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.allocatedSupportedSlicedInactiveResidueJetPMF_source_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.allocatedSupportedSlicedInactiveResidueJetPMF_source` (in `lean/OAI/Combinatorics/Progressions/Geometry/AllocatedSupportedSlicedInactiveSource.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B196` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Geometry/AllocatedSupportedSlicedInactiveSource.lean (declaration OAI.Erdos3.VectorPolynomial.allocatedSupportedSlicedInactiveResidueJetPMF_source)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B196

section

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

theorem allocatedSupportedSlicedInactiveResidueJetPMF_source_s2
    (hsmall : basisAxisScale (basis j) i ≤ S.value ^ (j.val + 1))
    (hlarge : 2 * inactiveDenominator
      (principalProfileSize (R j) (layerIntegerPrincipalSlots (G := G) B j i).card) ≤ basisAxisScale (basis j) i)
    (hsize : ∀ b v, (Fintype.card α + 1) * q ≤ H ⟨⟨j,Sum.inr i⟩,b,v⟩)
    (rows : Finset (Finset α)) (shift : rows → ℤ) :
    let sources := principalSupportedAxisSources B (layerSamplerDegree I n) H hH q hq r ⟨j,Sum.inr i⟩ hsize
    let lower := fun (b : B ⟨j,Sum.inr i⟩) (v : Fin (j.val + 1)) (a : Option α) =>
      if a = none then c ⟨⟨j,Sum.inr i⟩,b,v⟩ else 0
    let strides := fun (b : B ⟨j,Sum.inr i⟩) (v : Fin (j.val + 1)) (_ : Option α) => step ⟨⟨j,Sum.inr i⟩,b,v⟩
    (weightedCubeIntegerSource sources).toPMF.map (affineWeightedCubeIntegerSum sources lower strides rows shift) =
      allocatedSupportedSlicedResidueJetPMF B U basis hR hσ S q r H step c hH hsubset hcell j i rows shift := by
  sorry

end Erdos3.VectorPolynomial

end

end OAI
end
