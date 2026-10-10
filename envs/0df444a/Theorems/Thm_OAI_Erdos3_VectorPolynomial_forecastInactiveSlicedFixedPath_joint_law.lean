-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_forecastInactiveSlicedFixedPath_joint_law
-- name    : OAI.Erdos3.VectorPolynomial.forecastInactiveSlicedFixedPath_joint_law
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T17:27:27.182991+00:00
-- url     : https://prove2.me/theorems/8cd0f2d4-4489-4ced-a378-7fc720607379
-- title:
--   Joint law of fixed-coefficient jets on distinct small inactive axes
-- statement:
--   Let $m\in\mathbb N$, $G$ a finite type, $I\colon\mathrm{Fin}\,m\to$ Type a family of finite types with decidable equality, $n\colon\mathrm{Fin}\,m\to\mathbb N$, $B$ a family of finite types with decidable equality indexed by `LayerSamplerAxis I n` $=\Sigma_j\,I_j\oplus\mathrm{Fin}\,n_j$, $J\colon\mathrm{Fin}\,m\to$ Type finite types, $U_j$ a subspace of $\mathbb R^{J_j}$, `basis` $j$ a basis indexed by $\mathrm{Fin}\,n_j$ of the orthogonal complement of `euclideanSubspace (U j)`, $R,\sigma\colon\mathrm{Fin}\,m\to\mathbb R$ with $R_j>0$ and $\sigma_j>0$ (`hR`, `hσ`), and $S$ a `LayerSamplerScale B U basis R σ` (a structure bundling a positive natural number `S.value` with width and gap conditions). Let $\alpha$ be a finite type with decidable equality and $q\in\mathbb N$; write $\mathcal T=$ `PrincipalTupleIndex B (layerSamplerDegree I n)` (triples $\langle a,b,v\rangle$ with $b\in B(a)$ and $v<j+1$ for $a=\langle j,\_\rangle$). Let $r\colon\mathcal T\to\mathrm{Option}\,\alpha\to\mathbb Z/q$, $H,\mathrm{step}\colon\mathcal T\to\mathbb N$ with $H_t>0$ (`hH`) and `lower` $\colon\mathcal T\to\mathbb Z$, with `integerProgressionSupport (lower t) (step t) (H t)` $=\{\mathrm{lower}_t+\mathrm{step}_t\,i:0\le i<H_t\}\subseteq[0,\ $`allocatedPrincipalSides B U basis S t`$)$ for all $t$ (`hsubset`), and assume (`hcell`) that the event `principalResidueLabel q y = r` has positive mass under `principalTupleWeights B (layerSamplerDegree I n) H hH`; let `conditioned` be `containedSupportedProgressionLaw B (layerSamplerDegree I n) (allocatedPrincipalSides B U basis S) H step lower … hH hsubset q r hcell`, a `FiniteProbabilityWeights` on integer tuples $y$. Let $A$ be a finite type and `selected` $\colon A\to\Sigma_j\,\mathrm{Fin}\,n_j$ injective, with `basisAxisScale (basis (selected a).1) (selected a).2` $\le\texttt{S.value}^{(\mathrm{selected}\,a).1+1}$ for all $a$ (`hsmall`). For each $a$ let $c_a$ assign an integer to each element of `BoundedCoefficientExponent (LayerSamplerVariables G I n B) ((selected a).1 + 1)` (finitely supported exponents of degree at most $(\mathrm{selected}\,a).1+1$ in the variables $G\oplus\mathcal T$), with $c_a(d)$ in the support of `allocatedLayerIntegerPMFs B U basis hR hσ S (selected a).1 (selected a).2 d` for all $a,d$. Let $x\colon G\to$ `IntegerScalarCubeBox α S.value` and `rows` $\colon A\to$ `Finset (Finset α)`. Then the image of `conditioned` under
--   $$y\mapsto\Big(a\mapsto M_a(y)\,c_a\Big),\qquad M_a(y)=\texttt{boundedCoefficientJetMatrix}\ (\texttt{allocatedPhysicalCubeRoot}\ \ldots\ (\_\mapsto0)\ x\ y)\ (\texttt{allocatedPhysicalCubeDirections}\ \ldots\ x\ y)\ ((\mathrm{selected}\,a).1+1)\ (\mathrm{rows}\ a),$$
--   (an integer matrix with rows indexed by `rows a`, applied to the vector $c_a$) equals the dependent product over $a\in A$ of `allocatedSupportedSlicedResidueJetPMF B U basis hR hσ S q r H step lower hH hsubset hcell (selected a).1 (selected a).2 (rows a) shiftₐ`, where $\mathrm{shift}_a(t)=$ `booleanCoefficient` $(\_\mapsto c_a(\texttt{constantCoefficientSlot}))\ t$ $=\sum_{u\subseteq t}(-1)^{|t\setminus u|}\,c_a(\texttt{constantCoefficientSlot})$. Here `allocatedPhysicalCubeRoot` is the integer vector $k\mapsto$ (the `none` coordinate of $x_g$ or of $y_t$) and `allocatedPhysicalCubeDirections` the integer matrix of the `some i` coordinates, and `allocatedSupportedSlicedResidueJetPMF … j i rows shift` is the PMF obtained by drawing coefficients from the dependent product of `allocatedLayerIntegerPMFs … j i` over the principal coefficient slots of $b\in B\langle j,\mathrm{inr}\,i\rangle$, drawing $y$ from `conditioned`, and returning $\mathrm{shift}+\sum_b\mathrm{coeff}_b\cdot$ `integerBooleanBlockJet` of the coordinates of $y$ at $\langle\langle j,\mathrm{inr}\,i\rangle,b,\cdot\rangle$.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.forecastInactiveSlicedFixedPath_joint_law` in `lean/OAI/Combinatorics/Progressions/Sampling/ForecastInactiveSlicedFixedPath.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B145` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Sampling/ForecastInactiveSlicedFixedPath.lean#L86

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B145

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical Matrix

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
variable (q : ℕ) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (lower : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ)
variable (hH : ∀ t, 0 < H t)
variable (hsubset : ∀ t, integerProgressionSupport (lower t) (step t : ℤ) (H t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ))
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
  H hH).mass
    (Finset.univ.filter (fun y => principalResidueLabel q y = r)))

local notation "conditioned" => containedSupportedProgressionLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) H step lower
  (allocatedPrincipalSides_pos B U basis S) hH hsubset q r hcell

theorem forecastInactiveSlicedFixedPath_joint_law
    {A : Type*} [Fintype A] (selected : A → Σ j : Fin m, Fin (n j))
    (hselected : Function.Injective selected)
    (hsmall : ∀ a, basisAxisScale (basis (selected a).1) (selected a).2 ≤
      S.value ^ ((selected a).1.val + 1))
    (c : ∀ a, BoundedCoefficientExponent (LayerSamplerVariables G I n B)
      ((selected a).1.val + 1) → ℤ)
    (hc : ∀ a d, c a d ∈ (allocatedLayerIntegerPMFs B U basis hR hσ S
      (selected a).1 (selected a).2 d).support)
    (x : G → IntegerScalarCubeBox α S.value) (rows : A → Finset (Finset α)) :
    (conditioned).toPMF.map (fun y a =>
      boundedCoefficientJetMatrix (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y)
        (allocatedPhysicalCubeDirections B U basis S x y) ((selected a).1.val + 1)
        (fun t : rows a => (t : Finset α)) *ᵥ c a) =
      dependentProductPMF (fun a =>
        allocatedSupportedSlicedResidueJetPMF B U basis hR hσ S q r H step lower hH hsubset hcell
          (selected a).1 (selected a).2 (rows a)
          (fun t => booleanCoefficient (fun _ : Finset α => c a (constantCoefficientSlot _ _)) t)) := by
  sorry

end Erdos3.VectorPolynomial
end
end OAI
