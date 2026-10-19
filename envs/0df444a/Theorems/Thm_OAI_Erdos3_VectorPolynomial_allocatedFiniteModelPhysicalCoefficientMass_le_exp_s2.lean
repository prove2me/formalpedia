-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedFiniteModelPhysicalCoefficientMass_le_exp_s2
-- name    : OAI.Erdos3.VectorPolynomial.allocatedFiniteModelPhysicalCoefficientMass_le_exp_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T04:42:19.548258+00:00
-- url     : https://prove2.me/theorems/2c04fa69-58e4-47f5-b874-ef110d02f579
-- title:
--   An exponential bound on the total coefficient mass of the allocated finite-model physical expansion
-- statement:
--   **Setting.** Let $m \in \mathbb{N}$; let $G$ be a finite type; let $I_j$ ($j \in \mathrm{Fin}\,m$) be finite types, $n : \mathrm{Fin}\,m \to \mathbb{N}$, and $B_a$ finite types indexed by the sampler axes $a$ in `LayerSamplerAxis I n`; let $J_j$ be finite types, $U_j \subseteq \mathbb{R}^{J_j}$ subspaces and $b_j$ a basis, indexed by $\mathrm{Fin}(n_j)$, of the orthogonal complement of $U_j$; let $R, \sigma : \mathrm{Fin}\,m \to \mathbb{R}$ and $S$ a `LayerSamplerScale B U b R σ` (a structure defined by OpenAI). Let $\mathrm{dim} \in \mathbb{N}$ and let $\mathrm{rowSets}_j$ = `boundedBooleanJetRows (Fin dim) (j+1)` (a finite set of subsets of $\mathrm{Fin}\,\mathrm{dim}$, defined by OpenAI), with $\mathrm{rowTypes}_j$ its subtype. Let $E_j$ be finite types, $x : G \to$ `IntegerScalarCubeBox (Fin dim) S.value`, $y_0$ a `PrincipalIntegerTuples` element (for the sides `allocatedPrincipalSides B U b S`), and $q, d, \mathrm{period}$ natural numbers with $d \ne 0$ and $\mathrm{period} \ne 0$. Assume (hypothesis $h_b$) that for each $j$ the $\mathbb{Z}$-span of $b_j$ is the projected integer lattice `projectedIntegerLattice` of $U_j$, and let $bW_j$ be a $\mathbb{Z}$-basis, indexed by $E_j$, of the section of the standard lattice $\mathbb{Z}^{J_j}$ by $U_j$. Let $\nu$ = `allocatedProductIdealNormalizer B U b S rowSets` (a real number defined by OpenAI). Let $e$ assign to each grid axis $a$ (an axis with `allocatedGridAxis U b S.value a`) a `ScalarSiteExpansion` over $\mathrm{Finset}(\mathrm{Fin}\,\mathrm{dim})$ (defined by OpenAI: a finite family of terms with complex coefficients, periods and factor functions). Let $T$ be a finite type and $a : T \to \mathbb{C}$.
--
--   Write $\Lambda$ for the finite type $\bigl(\prod_j (\mathbb{Z}/\mathrm{period})^{\mathrm{Fin}(n_j)}\bigr) \times \bigl(\prod_j (\mathbb{Z}/\mathrm{period})^{E_j}\bigr)$, labels for functions $\mathrm{Finset}(\mathrm{Fin}\,\mathrm{dim}) \to \Lambda$, $c(\mathrm{label}, i)$ for `allocatedProductMaskedIdealCoefficient B U b S rowSets x y₀ q d period a label i` ($= \nu^{-1} \cdot \mathrm{mask}(\mathrm{label}) \cdot a_i$, defined by OpenAI), $N_S = 2^{\mathrm{dim}}$ for the number of subsets of $\mathrm{Fin}\,\mathrm{dim}$, $\Pi$ = `coefficientDeckPeriodCap rowTypes E period` $= \prod_j \prod_{E_j} \mathrm{period}^{|\mathrm{rowTypes}_j|}$, and $|\mathrm{Ax}|$ for the number of sampler axes.
--
--   **Statement.** Let $M, F, A, P_{\mathrm{per}}, O_p$ be reals with:
--   - $0 \le M$;
--   - $|\nu^{-1}| \cdot M^{|\mathrm{Ax}|} \cdot \Pi \le e^{F}$;
--   - $\mathrm{period} \le e^{P_{\mathrm{per}}}$;
--   - $\sum_{\mathrm{label}} \sum_{i \in T} |c(\mathrm{label}, i)| \le |\nu^{-1}| \cdot |\Lambda|^{N_S} \cdot M^{|\mathrm{Ax}|} \cdot \Pi \cdot e^{A}$.
--
--   Let $N_t, V, H_s$ be real-valued functions on the grid axes and $L_g \ge 0$, and assume that for every grid axis $a$, `(e a).Bounds (N_t a) (V a) (exp O_p) L_g (H_s a)` holds (defined by OpenAI: $e_a$ has at most $N_t(a)$ terms, all periods are positive and at most $V(a)$, the coefficients have total absolute value at most $e^{O_p}$, every factor has absolute value at most $1$, is $L_g$-Lipschitz, and vanishes at $|x| \ge H_s(a)$). Then
--   $$\sum_{\mathrm{label}} \sum_{i \in T} \sum_{k} \bigl| 2^{N_S}\, c(\mathrm{label}, i) \cdot \texttt{coverSiteCoefficient}\ e\ k \bigr| \le \exp\Bigl(2 N_S + F + N_S \Bigl(\sum_j |J_j|\Bigr) P_{\mathrm{per}} + A + |\mathrm{GridAx}| \cdot O_p\Bigr),$$
--   where $k$ ranges over choices of one term of $e_a$ for each grid axis $a$, `coverSiteCoefficient e k` (defined by OpenAI) is $2^{N_S}$ times the product of the chosen coefficients, and $|\mathrm{GridAx}|$ is the number of grid axes.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.allocatedFiniteModelPhysicalCoefficientMass_le_exp_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.allocatedFiniteModelPhysicalCoefficientMass_le_exp` (in `lean/OAI/Combinatorics/Progressions/Probability/AllocatedPhysicalExpansionMass.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B216` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Probability/AllocatedPhysicalExpansionMass.lean (declaration OAI.Erdos3.VectorPolynomial.allocatedFiniteModelPhysicalCoefficientMass_le_exp)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B216

section

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ}
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))

local notation "rowTypes" => (fun j : Fin m => {t : Finset (Fin dim) // t ∈ rowSets j})

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
variable (q d period : ℕ) [NeZero d] [NeZero period]
variable (r : ℝ≥0) (hr : 0 < r)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

local notation "inverseNormalizer" => ((allocatedProductIdealNormalizer B U b S rowSets : ℝ) : ℂ)⁻¹

attribute [local instance] ScalarSiteExpansion.termFinite
attribute [local instance 2000] fullGridCoverAxisDecidableEq

variable (e : {a // allocatedGridAxis (I := I) U b S.value a} → ScalarSiteExpansion.{0,0} (Finset (Fin dim)))

variable {T : Type*} [Fintype T] (a : T → ℂ)
variable (f : T → Finset (Fin dim) → (LayerSamplerAxis I n → ℝ) → ℂ)

variable {X : Type*} (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j e, coefficients (p j) e ∈ U j)

include hb bW in

theorem allocatedFiniteModelPhysicalCoefficientMass_le_exp_s2
    {M F A Pper Op : ℝ} (hM : 0 ≤ M)
    (hpref : ‖inverseNormalizer‖ *
      (M ^ Fintype.card (LayerSamplerAxis I n) * coefficientDeckPeriodCap rowTypes E period) ≤ Real.exp F)
    (hperiod : (period : ℝ) ≤ Real.exp Pper)
    (hA : (∑ label : Finset (Fin dim) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)),
      ∑ i, ‖allocatedProductMaskedIdealCoefficient B U b S rowSets x y₀ q d period a label i‖) ≤
      ‖inverseNormalizer‖ *
        ((Fintype.card ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)) : ℝ) ^
          Fintype.card (Finset (Fin dim)) *
          (M ^ Fintype.card (LayerSamplerAxis I n) * coefficientDeckPeriodCap rowTypes E period) * Real.exp A))
    {Nt V Hs : {a // allocatedGridAxis (I := I) U b S.value a} → ℝ} {Lg : ℝ≥0}
    (he : ∀ a, (e a).Bounds (Nt a) (V a) (Real.exp Op) Lg (Hs a)) :
    (∑ label : Finset (Fin dim) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)),
      ∑ i, ∑ k, ‖((2 : ℂ) ^ Fintype.card (Finset (Fin dim)) *
        allocatedProductMaskedIdealCoefficient B U b S rowSets x y₀ q d period a label i) * coverSiteCoefficient e k‖) ≤
      Real.exp (2 * Fintype.card (Finset (Fin dim)) + F +
        Fintype.card (Finset (Fin dim)) * ((∑ j, Fintype.card (J j) : ℕ) * Pper) + A +
        Fintype.card {a // allocatedGridAxis (I := I) U b S.value a} * Op) := by
  sorry

end Erdos3.VectorPolynomial

end

end OAI
end
