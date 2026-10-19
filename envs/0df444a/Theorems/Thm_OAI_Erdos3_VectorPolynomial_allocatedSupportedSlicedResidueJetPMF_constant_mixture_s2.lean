-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedSupportedSlicedResidueJetPMF_constant_mixture_s2
-- name    : OAI.Erdos3.VectorPolynomial.allocatedSupportedSlicedResidueJetPMF_constant_mixture_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T04:28:05.715487+00:00
-- url     : https://prove2.me/theorems/64ea6f28-5a1b-4ce2-a999-f070f4173560
-- title:
--   On a grid axis, the conditioned jet-image PMF is a mixture of supported sliced residue jet PMFs over the constant coefficient
-- statement:
--   Fix the data of OpenAI's allocated layer-sampler setup: a natural number $m$; finite types $G$, $I_j$ (with decidable equality) and $J_j$ for $j < m$, $B(a)$ for each layer-sampler axis $a$ (finite, with decidable equality) and $\alpha$ (finite, with decidable equality); dimensions $n_j$; subspaces $U_j \subseteq \mathbb{R}^{J_j}$; bases `basis j` (indexed by $\{0, \dots, n_j - 1\}$) of the orthogonal complement of $U_j$; reals $R_j > 0$, $\sigma_j > 0$; and a `LayerSamplerScale B U basis R σ` $S$. Let $q$ be a natural number, $r$ a map from `PrincipalTupleIndex B (layerSamplerDegree I n)` to residue vectors $\texttt{Option}\ \alpha \to \mathbb{Z}/q$, and $H, \mathrm{step}$ (natural-valued) and $c$ (integer-valued) functions on that index set with $H(t) > 0$, ($hsubset$) each progression `integerProgressionSupport (c t) (step t) (H t)` contained in $[0, \texttt{allocatedPrincipalSides B U basis S}\ t)$, and ($hcell$) the residue cell $\{y : \texttt{principalResidueLabel q}\ y = r\}$ of positive mass under `principalTupleWeights B (layerSamplerDegree I n) H hH`. Let `conditioned` be OpenAI's probability law `containedSupportedProgressionLaw B (layerSamplerDegree I n) (allocatedPrincipalSides B U basis S) H step c … q r hcell` on principal integer tuples (the progression law conditioned on the residue cell $r$).
--
--   Let $j < m$ and $i < n_j$, and assume the axis $(j, \mathrm{inr}\ i)$ is a grid axis, i.e. `allocatedGridAxis U basis S.value ⟨j, inr i⟩` holds. Let `rows` be a finite set of subsets of $\alpha$ and $x : G \to$ `IntegerScalarCubeBox α S.value`. Then the following two probability mass functions are equal:
--   - the bind of `conditioned` (as a PMF) with $y \mapsto \texttt{integerMatrixImagePMF}(M_y, \pi_{j,i})$, where $M_y$ = `boundedCoefficientJetMatrix (allocatedPhysicalCubeRoot B U basis S 0 x y) (allocatedPhysicalCubeDirections B U basis S x y) (j+1) (t ↦ t)` (rows indexed by `rows`) and $\pi_{j,i}$ = `allocatedLayerIntegerPMFs B U basis hR hσ S j i` (`integerMatrixImagePMF M π` is the law of $M v$ when the entries of $v$ are drawn independently from $\pi$);
--   - the bind of the PMF $\pi_{j,i}(\texttt{principalCoefficientChoice (layerSamplerDegree I n) <j, inr i> none})$ with $z \mapsto$ `allocatedSupportedSlicedResidueJetPMF B U basis hR hσ S q r H step c hH hsubset hcell j i rows (t ↦ booleanCoefficient (_ ↦ z) t)`.
--
--   All named objects are defined by OpenAI.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.allocatedSupportedSlicedResidueJetPMF_constant_mixture_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.allocatedSupportedSlicedResidueJetPMF_constant_mixture` (in `lean/OAI/Combinatorics/Progressions/Lattices/AllocatedSupportedSlicedResidueJet.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B196` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Lattices/AllocatedSupportedSlicedResidueJet.lean (declaration OAI.Erdos3.VectorPolynomial.allocatedSupportedSlicedResidueJetPMF_constant_mixture)

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

local notation "conditioned" => containedSupportedProgressionLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) H step c (allocatedPrincipalSides_pos B U basis S) hH hsubset q r hcell

theorem allocatedSupportedSlicedResidueJetPMF_constant_mixture_s2
    (hgrid : allocatedGridAxis (I := I) U basis S.value ⟨j, Sum.inr i⟩)
    (rows : Finset (Finset α)) (x : G → IntegerScalarCubeBox α S.value) :
    (conditioned).toPMF.bind (fun y =>
      integerMatrixImagePMF (boundedCoefficientJetMatrix
        (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y)
        (allocatedPhysicalCubeDirections B U basis S x y) (j.val + 1)
        (fun t : rows => (t : Finset α))) (allocatedLayerIntegerPMFs B U basis hR hσ S j i)) =
      (allocatedLayerIntegerPMFs B U basis hR hσ S j i
        (principalCoefficientChoice (G := G) (layerSamplerDegree I n) ⟨j, Sum.inr i⟩ none)).bind
        (fun z => allocatedSupportedSlicedResidueJetPMF B U basis hR hσ S q r H step c hH hsubset hcell j i rows
          (fun t => booleanCoefficient (fun _ : Finset α => z) t)) := by
  sorry

end Erdos3.VectorPolynomial

end

end OAI
end
