-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_forecastInactive_sliced_fixed_grid_mass_le
-- name    : OAI.Erdos3.VectorPolynomial.forecastInactive_sliced_fixed_grid_mass_le
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-09T22:39:11.065284+00:00
-- url     : https://prove2.me/theorems/d2409c37-25d3-4a33-b54a-c2f87cc6ea68
-- title:
--   Point-mass bound for fixed-coefficient outputs on small inactive grid axes
-- statement:
--   Let $m\in\mathbb N$, $G$ a finite type, $I\colon\mathrm{Fin}\,m\to$ Type a family of finite types with decidable equality, $n\colon\mathrm{Fin}\,m\to\mathbb N$, $B$ a family of finite types with decidable equality indexed by `LayerSamplerAxis I n` $=\Sigma_j\,I_j\oplus\mathrm{Fin}\,n_j$, $J\colon\mathrm{Fin}\,m\to$ Type finite types, $U_j$ a subspace of $\mathbb R^{J_j}$, `basis` $j$ a basis indexed by $\mathrm{Fin}\,n_j$ of the orthogonal complement of `euclideanSubspace (U j)`, $R,\sigma\colon\mathrm{Fin}\,m\to\mathbb R$ with $R_j>0$ and $\sigma_j>0$ (`hR`, `hσ`), and $S$ a `LayerSamplerScale B U basis R σ` (a structure bundling a positive natural number `S.value` with width and gap conditions). Write $\mathcal T=$ `PrincipalTupleIndex B (layerSamplerDegree I n)` and `sides` $=$ `allocatedPrincipalSides B U basis S` (a positive natural number for each index). Let $H,\mathrm{step}\colon\mathcal T\to\mathbb N$ with $H_t>0$ (`hH`) and $c\colon\mathcal T\to\mathbb Z$ with `integerProgressionSupport (c t) (step t) (H t)` $=\{c_t+\mathrm{step}_t\,i:0\le i<H_t\}\subseteq[0,\mathrm{sides}_t)$ (`hsubset`). Let $A$ be a finite type and `selected` $\colon A\to\Sigma_j\,\mathrm{Fin}\,n_j$ injective; for $a\in A$ write $(j_a,i_a)=\mathrm{selected}(a)$ and $a^\ast=\langle j_a,\mathrm{inr}\,i_a\rangle$. Let $\delta,P$ be reals and $H_{\mathrm{child}}\in\mathbb N$ with $\delta>0$. Assume: (`hreg`) for each $a$, either $\mathrm{sides}_{\langle a^\ast,b_0,v_0\rangle}<H_{\mathrm{child}}$ for some $b_0,v_0$, or both $\delta\cdot\mathrm{sides}_{\langle a^\ast,b,v\rangle}\le H_{\langle a^\ast,b,v\rangle}$ and $0<\mathrm{step}_{\langle a^\ast,b,v\rangle}$ for all $b,v$; (`hsmall`) `basisAxisScale (basis jₐ) iₐ` $\le\texttt{S.value}^{j_a+1}$; (`hgrid`) `allocatedGridAxis U basis S.value a*`. Let `coefficients` $a$ assign an integer to each element of `BoundedCoefficientExponent (LayerSamplerVariables G I n B) (jₐ + 1)`, lying in the support of `allocatedLayerIntegerPMFs B U basis hR hσ S jₐ iₐ d` at each $d$. Let $L\ge0$ with `Real.smoothTransition` $L$-Lipschitz, $1\le P$, `scalarCubePrimitiveEnvelope Empty L 1 0 1` $\le P$ (an explicit real number), $\mathrm{step}_{\langle a^\ast,b,v\rangle}\le P$ for all $a,b,v$, `uniformSpectrumBlockCount jₐ 1 (jₐ + 1)` $\le|B(a^\ast)|$ for all $a$, and let $C_{\mathrm{actual}}\ge0$ be real. Put, for each $a$: $\mathrm{degree}_a=j_a+1$; $\mathrm{height}_a=$ `basisAxisScale (basis jₐ) iₐ`; $\mathrm{denom}_a=$ `inactiveDenominator (principalProfileSize (R jₐ) |layerIntegerPrincipalSlots B jₐ iₐ|)` $=\max(1,\lceil\gamma^{-1}\rceil)$ with $\gamma=R_{j_a}/(8(|\cdot|+1))$; $\mathrm{torus}_a=$ `blockTorusFactor 0 degreeₐ |B(a*)| 1` (a natural number); $V_a=\mathrm{torus}_a\cdot\mathrm{denom}_a\cdot2^{\mathrm{degree}_a}/\delta^{\mathrm{degree}_a}$; $\mathrm{cap}_a=$ `uniformSpectrumAbsoluteCap jₐ 1 degreeₐ P Vₐ Vₐ` (a real number); and $\mathrm{cutoff}_a=\max\big($`allocatedSlicedGridHeightCutoff B jₐ iₐ ⌈1/δ⌉₊`$,\ \mathrm{denom}_a2^{\mathrm{degree}_a}H_{\mathrm{child}}^{\mathrm{degree}_a}+2\,\mathrm{denom}_a\big)$ (the first a natural number depending on $B$, $R$, $j_a$, $i_a$). Then, if $\max(\mathrm{cutoff}_a,\mathrm{cap}_a)\le C_{\mathrm{actual}}$ for every $a$, for every $x\colon G\to$ `IntegerScalarCubeBox Empty S.value` and every $z\colon A\to\mathbb Z$,
--   $$\Big(\prod_a\mathrm{height}_a\Big)\cdot\Pr_{y\sim\lambda}\big[\texttt{forecastInactiveFixedOutput}\ B\ U\ \mathrm{basis}\ S\ \mathrm{selected}\ \mathrm{coefficients}\ x\ y=(a\mapsto(\_\mapsto z_a))\big]\le C_{\mathrm{actual}}^{|A|},$$
--   the probability being `fiberMean … (fun _ => 1)`, where $\lambda$ is the push-forward of `principalTupleWeights B (layerSamplerDegree I n) H hH` (with $\alpha=$ Empty) under `containedProgressionTupleMap B (layerSamplerDegree I n) sides H step c … hsubset` (`fiberLaw`), and `forecastInactiveFixedOutput … x y` sends $a$ to the integer vector (indexed by the single subset of Empty) $M_a(y)\,\mathrm{coefficients}_a$, with $M_a(y)=$ `boundedCoefficientJetMatrix` of `allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y` and `allocatedPhysicalCubeDirections B U basis S x y` in degree $j_a+1$.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.forecastInactive_sliced_fixed_grid_mass_le` in `lean/OAI/Combinatorics/Progressions/Sampling/ForecastInactiveSlicedFixedGridCap.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B144`, `OAIErdos3B145` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Sampling/ForecastInactiveSlicedFixedGridCap.lean#L27

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B144
import Definitions.Def_OAIErdos3B145

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
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
variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ t, 0 < H t)
variable (hsubset : ∀ t, integerProgressionSupport (c t) (step t : ℤ) (H t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ))
variable {A : Type*} [Fintype A]

theorem forecastInactive_sliced_fixed_grid_mass_le
    (selected : A → Σ j : Fin m, Fin (n j))
    (hselected : Function.Injective selected)
    (δ P : ℝ) (Hchild : ℕ) (hδ : 0 < δ)
    (hreg : ∀ a, (∃ b0 v0,
      allocatedPrincipalSides B U basis S ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b0,v0⟩ < Hchild) ∨
      ((∀ b v, δ * allocatedPrincipalSides B U basis S ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b,v⟩ ≤
        (H ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b,v⟩ : ℝ)) ∧
       (∀ b v, 0 < step ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b,v⟩)))
    (hsmall : ∀ a, basisAxisScale (basis (selected a).1) (selected a).2 ≤
      S.value ^ ((selected a).1.val + 1))
    (hgrid : ∀ a, allocatedGridAxis (I := I) U basis S.value ⟨(selected a).1, Sum.inr (selected a).2⟩)
    (coefficients : ∀ a, BoundedCoefficientExponent (LayerSamplerVariables G I n B)
      ((selected a).1.val + 1) → ℤ)
    (hcoefficients : ∀ a d, coefficients a d ∈ (allocatedLayerIntegerPMFs B U basis hR hσ S
      (selected a).1 (selected a).2 d).support)
    (L : ℝ≥0) (hL : LipschitzWith L Real.smoothTransition)
    (hP : 1 ≤ P) (hsP : scalarCubePrimitiveEnvelope Empty L 1 0 1 ≤ P)
    (hstride : ∀ a b v, (step ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b,v⟩ : ℝ) ≤ P)
    (hB : ∀ a, uniformSpectrumBlockCount (selected a).1.val 1 ((selected a).1.val + 1) ≤
      Fintype.card (B ⟨(selected a).1, Sum.inr (selected a).2⟩))
    (Cactual : ℝ) (_hCactual : 0 ≤ Cactual) :
    let degree := fun a => (selected a).1.val + 1
    let height := fun a => basisAxisScale (basis (selected a).1) (selected a).2
    let denom := fun a => inactiveDenominator (principalProfileSize (R (selected a).1)
      (Finset.card (layerIntegerPrincipalSlots (G := G) B (selected a).1 (selected a).2)))
    let torus := fun a => blockTorusFactor (Fintype.card Empty) (degree a)
      (Fintype.card (B ⟨(selected a).1, Sum.inr (selected a).2⟩)) 1
    let V := fun a => (torus a : ℝ) * ((denom a : ℝ) * 2 ^ degree a) / δ ^ degree a
    let cap := fun a => uniformSpectrumAbsoluteCap (selected a).1.val 1 (degree a) P (V a) (V a)
    let cutoff := fun a => max (allocatedSlicedGridHeightCutoff (G := G) B (R := R)
      (selected a).1 (selected a).2 (Nat.ceil ((1 : ℝ) / δ)))
      (denom a * 2 ^ degree a * Hchild ^ degree a + 2 * denom a)
    (∀ a, max (cutoff a : ℝ) (cap a) ≤ Cactual) →
    ∀ (x : G → IntegerScalarCubeBox Empty S.value) (z : A → ℤ),
    let p := principalTupleWeights (α := Empty) B (layerSamplerDegree I n) H hH
    let map := containedProgressionTupleMap B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U basis S) H step c (allocatedPrincipalSides_pos B U basis S) hsubset
    let law := p.fiberLaw map
    (∏ a, (height a : ℝ)) * law.fiberMean
      (forecastInactiveFixedOutput B U basis S selected coefficients x)
      (fun a _ => z a) (fun _ => 1) ≤ Cactual ^ Fintype.card A := by
  sorry

end Erdos3.VectorPolynomial
end
end OAI
