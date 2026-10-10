-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedSupportedSlicedGridDensity_absolute_cap
-- name    : OAI.Erdos3.VectorPolynomial.allocatedSupportedSlicedGridDensity_absolute_cap
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-09T16:11:57.447807+00:00
-- url     : https://prove2.me/theorems/1c6154a7-4de7-429f-9914-d08c3528b4d8
-- title:
--   Absolute summability cap for grid coefficients on an active grid axis
-- statement:
--   Let $m\in\mathbb N$, $G$ a finite type, $I\colon\mathrm{Fin}\,m\to$ Type a family of finite types, $n\colon\mathrm{Fin}\,m\to\mathbb N$, $B$ a family of finite types indexed by `LayerSamplerAxis I n` $=\Sigma_j\,I_j\oplus\mathrm{Fin}\,n_j$, $J\colon\mathrm{Fin}\,m\to$ Type finite types, $U_j$ a subspace of $\mathbb R^{J_j}$, `basis` $j$ a basis indexed by $\mathrm{Fin}\,n_j$ of the orthogonal complement of `euclideanSubspace (U j)`, $R\colon\mathrm{Fin}\,m\to\mathbb R$ with $R_j>0$ (`hR`), $\sigma\colon\mathrm{Fin}\,m\to\mathbb R$, and $S$ a `LayerSamplerScale B U basis R σ` (a structure bundling a positive natural number `S.value` with width and gap conditions). Let $\alpha$ be a finite type with decidable equality and $q>0$ (`hq`); write $\mathcal T=$ `PrincipalTupleIndex B (layerSamplerDegree I n)`. Let $r\colon\mathcal T\to\mathrm{Option}\,\alpha\to\mathbb Z/q$, $H,\mathrm{step}\colon\mathcal T\to\mathbb N$ with $H_t>0$ (`hH`), and $c\colon\mathcal T\to\mathbb Z$. Fix $j\in\mathrm{Fin}\,m$, $i\in\mathrm{Fin}\,n_j$, write $a_0=\langle j,\mathrm{inr}\,i\rangle$ and $\mathrm{height}=$ `basisAxisScale (basis j) i`, and assume $\texttt{S.value}^{j+1}<\mathrm{height}$ (`hactive`) and $(|\alpha|+1)q\le H_{\langle a_0,b,v\rangle}$ for all $b,v$ (`hsize`). Let `coeff` be the constant family $b\mapsto$ `allocatedPrincipalNormalizedSource B U basis hR S j i hactive` (a `NormalizedScalarCubeSource Empty`), `sources` $=$ `principalSupportedAxisSources B (layerSamplerDegree I n) H hH q hq r a₀ hsize` (a `NormalizedScalarCubeSource α` for each $b\in B(a_0)$ and $v<j+1$), $\mathrm{lower}(b,v,a)=c_{\langle a_0,b,v\rangle}$ if $a=\mathrm{none}$ and $0$ otherwise, $\mathrm{strides}(b,v,\_)=\mathrm{step}_{\langle a_0,b,v\rangle}$, and $\gamma=$ `principalProfileSize (R j) |layerIntegerPrincipalSlots B j i|` $=R_j/(8(|\cdot|+1))$. Assume `allocatedGridAxis U basis S.value a₀` (`hgrid`); $\delta>0$ with $\delta\cdot\texttt{S.value}\le H_{\langle a_0,b,v\rangle}$ and $0<\mathrm{step}_{\langle a_0,b,v\rangle}$ for all $b,v$; $A\ge0$ with `Real.smoothTransition` $A$-Lipschitz; a real $P$ with `scalarCubePrimitiveEnvelope Empty A 16 (128 * probabilityProfileLipschitz) 1` $\le P$, `scalarCubePrimitiveEnvelope α A 1 0 q` $\le P$ and $\mathrm{step}_{\langle a_0,b,v\rangle}\,q\le P$ for all $b,v$ (`probabilityProfileLipschitz` is a nonnegative real constant); a real $C\ge0$ and a natural number $M\ne0$ with $M\le C\cdot\mathrm{height}$; and `rows` a `Finset (Finset α)` whose members have at most $j+1$ elements, with `positiveModerateSpectrumBlockCount j |rows| ((layerTailDegree m + 1) * |rows|)` $\le|B(a_0)|$. Let $V=(C/(2\gamma))/\delta^{j+1}$, $t=($`layerTailDegree m`$+1)\,|\mathrm{rows}|$ and $W=C^{|\mathrm{rows}|}/\delta^{t}$. Then
--   $$\sum_{k\colon\mathrm{rows}\to\mathrm{Fin}\,M}\Big\|\prod_{b\in B(a_0)}\texttt{weightedAffineModerateGridCoefficient}\ (\mathrm{coeff}\ b)\ (\mathrm{sources}\ b)\ (\mathrm{lower}\ b)\ (\mathrm{strides}\ b)\ 0\ M\ \mathrm{rows}\ k\Big\|\le\texttt{positiveModerateSpectrumCardBudget}\ j\ |\mathrm{rows}|\ t\ P\ V\ W\ 1+1,$$
--   where `weightedAffineModerateGridCoefficient c s u v shift M J k` is the complex number $\mathbb E_{z\sim c}\,\mathbb E_{x\sim\prod_v s_v}\,e\big((\mathrm{shift}+z_{\mathrm{none}})\cdot$ `booleanBlockPhase (gridJetFrequency M J k)` of the affine coordinates `affineCubeCoordinates (u v) (v v) x`$\big)$ ($e$ the character into the circle), and `positiveModerateSpectrumCardBudget` is an explicit real number.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.allocatedSupportedSlicedGridDensity_absolute_cap` in `lean/OAI/Combinatorics/Progressions/Lattices/AllocatedSupportedSlicedResidueGrid.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B145` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Lattices/AllocatedSupportedSlicedResidueGrid.lean#L474

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B145

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical NNReal

end Erdos3

end

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
variable (hsize : ∀ t, (Fintype.card α + 1) * q ≤ H t)
variable (j : Fin m) (i : Fin (n j))

local notation "conditioned" => containedProgressionResidueLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) H step c (allocatedPrincipalSides_pos B U basis S) hH hsubset q hq r hsize

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

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
variable (hsize : ∀ t, (Fintype.card α + 1) * q ≤ H t)
variable (j : Fin m) (i : Fin (n j))

variable (hactive : S.value ^ (j.val + 1) < basisAxisScale (basis j) i)

local notation "coeff" => (fun _ : B (Sigma.mk j (Sum.inr i)) =>
  allocatedPrincipalNormalizedSource B U basis hR S j i hactive)
local notation "sources" => principalSupportedAxisSources B (layerSamplerDegree I n) H hH q hq r
  (Sigma.mk j (Sum.inr i)) (fun b v => hsize (Sigma.mk (Sigma.mk j (Sum.inr i)) (Prod.mk b v)))
local notation "lower" => (fun (b : B (Sigma.mk j (Sum.inr i))) (v : Fin (Fin.val j + 1)) (a : Option α) =>
  ite (a = none) (c (Sigma.mk (Sigma.mk j (Sum.inr i)) (Prod.mk b v))) 0)
local notation "strides" => (fun (b : B (Sigma.mk j (Sum.inr i))) (v : Fin (Fin.val j + 1)) (_ : Option α) =>
  step (Sigma.mk (Sigma.mk j (Sum.inr i)) (Prod.mk b v)))
local notation "gamma" => principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

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

variable (hactive : S.value ^ (j.val + 1) < basisAxisScale (basis j) i)
variable (hsize : ∀ b v, (Fintype.card α + 1) * q ≤ H ⟨⟨j,Sum.inr i⟩,b,v⟩)

local notation "coeff" => (fun _ : B (Sigma.mk j (Sum.inr i)) =>
  allocatedPrincipalNormalizedSource B U basis hR S j i hactive)
local notation "sources" => principalSupportedAxisSources B (layerSamplerDegree I n) H hH q hq r
  (Sigma.mk j (Sum.inr i)) hsize
local notation "lower" => (fun (b : B (Sigma.mk j (Sum.inr i))) (v : Fin (Fin.val j + 1)) (a : Option α) =>
  ite (a = none) (c (Sigma.mk (Sigma.mk j (Sum.inr i)) (Prod.mk b v))) 0)
local notation "strides" => (fun (b : B (Sigma.mk j (Sum.inr i))) (v : Fin (Fin.val j + 1)) (_ : Option α) =>
  step (Sigma.mk (Sigma.mk j (Sum.inr i)) (Prod.mk b v)))
local notation "gamma" => principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i))

omit [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)] in
theorem allocatedSupportedSlicedGridDensity_absolute_cap
    (hgrid : allocatedGridAxis (I := I) U basis S.value ⟨j, Sum.inr i⟩)
    {δ : ℝ} (hδ : 0 < δ)
    (hlength : ∀ b v, δ * S.value ≤ (H ⟨⟨j,Sum.inr i⟩,b,v⟩ : ℝ))
    (hstep : ∀ b v, 0 < step ⟨⟨j,Sum.inr i⟩,b,v⟩)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) (P : ℝ)
    (hcP : scalarCubePrimitiveEnvelope Empty A 16 (128 * probabilityProfileLipschitz) 1 ≤ P)
    (hsP : scalarCubePrimitiveEnvelope α A 1 0 q ≤ P)
    (hstride : ∀ b v, ((step ⟨⟨j,Sum.inr i⟩,b,v⟩ * q : ℕ) : ℝ) ≤ P)
    {C : ℝ} {M : ℕ} [NeZero M] (hC : 0 ≤ C)
    (hMK : (M : ℝ) ≤ C * basisAxisScale (basis j) i)
    (rows : Finset (Finset α)) (hrows : ∀ t ∈ rows, t.card ≤ j.val + 1)
    (hB : positiveModerateSpectrumBlockCount j.val rows.card
      ((layerTailDegree m + 1) * rows.card) ≤ Fintype.card (B ⟨j, Sum.inr i⟩))
    :
    let V := (C / (2 * gamma)) / δ ^ (j.val + 1)
    let t := (layerTailDegree m + 1) * rows.card
    let W := C ^ rows.card / δ ^ t
    (∑ k, ‖∏ b, weightedAffineModerateGridCoefficient (coeff b) (sources b)
      (fun v a => (lower b v a : ℝ)) (strides b) 0 M rows k‖) ≤
        positiveModerateSpectrumCardBudget j.val rows.card t P V W 1 + 1 := by
  sorry

end Erdos3.VectorPolynomial
end
end OAI
