-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_exists_allocatedCanonicalSlice_bounded_ambient_s2
-- name    : OAI.Erdos3.VectorPolynomial.exists_allocatedCanonicalSlice_bounded_ambient_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T04:46:14.117285+00:00
-- url     : https://prove2.me/theorems/f6122590-1fb7-454e-8c26-c2df2713db51
-- title:
--   The canonical-slice covered profile mean is close to a bounded Lipschitz torus function
-- statement:
--   Fix the section data: a natural number $m$; a finite type $G$; finite types $I_j$ and natural numbers $n_j$ ($j \in \mathrm{Fin}\,m$); finite types $B_a$ with decidable equality over the axes $a$ of `LayerSamplerAxis I n` (the sigma type $\Sigma_j\, I_j \oplus \mathrm{Fin}(n_j)$); finite types $J_j$, real subspaces $U_j \subseteq \mathbb R^{J_j}$ and bases $b_j$ (indexed by $\mathrm{Fin}\,n_j$) of the orthogonal complements of `euclideanSubspace (U j)`; real functions $R, \sigma$ on $\mathrm{Fin}\,m$ with $R_j > 0$ (hR) and $\sigma_j > 0$ (hσ); a `LayerSamplerScale` $S$ (a structure bundling a positive natural number $S.\mathrm{value}$ with width and gap inequalities); $\mathrm{dim} \in \mathbb N$ and finite families $\mathrm{rowSets}_j$ of finsets of $\mathrm{Fin}\,\mathrm{dim}$ (rowTypes$_j$ its subtype, rows$_j$ the inclusion); grid the predicate `allocatedGridAxis U b S.value`; finite types $E_j$; a point $x : G \to$ `IntegerScalarCubeBox (Fin dim) S.value`; a tuple $y_0$ in `PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S)`; $q \in \mathbb N$ and natural numbers $d, \mathrm{period} \ne 0$; $r \in \mathbb R_{\ge 0}$ with $r > 0$ (hr); $\mathbb Z$-span of $b_j$ equal to `projectedIntegerLattice (euclideanSubspace (U j))` (hb); orthonormal bases $o_j$ of `euclideanSubspace (U j)` indexed by $I_j$; $\mathbb Z$-bases $bW_j$ (indexed by $E_j$) of `latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))`; $C : \mathrm{Fin}\,m \to \mathbb R$ with $C_j \ge 0$ (hC), $\|(\texttt{normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)})^{-1}v\| \le C_j\|v\|$ (hchart) and $(|\mathrm{rowSets}_j|+1)\cdot 2^{\mathrm{dim}}\cdot C_j(|I_j|+1)\cdot 2rR_j \le 1/4$ (hbudget) for all $j$; $\rho \in \mathbb R_{\ge 0}$ and real functions center, width on `PrincipalAxisParameter (¬ grid)` (with $\alpha = \mathrm{Fin}\,\mathrm{dim}$); $H, \mathrm{step} : \mathrm{FullInput} \to \mathbb N$ and $c : \mathrm{FullInput} \to \mathbb Z$ (FullInput $=$ `PrincipalTupleIndex B (layerSamplerDegree I n)`) with $H > 0$ (hH) and each `integerProgressionSupport (c t) (step t) (H t)` contained in $[0,$ `allocatedPrincipalSides B U b S t`$)$ (hsubset); a residue label $\lambda : \mathrm{FullInput} \to \mathrm{Option}(\mathrm{Fin}\,\mathrm{dim}) \to \mathbb Z/q$ whose cell has positive mass under `principalTupleWeights B (layerSamplerDegree I n) H hH` (hcell); $M_k \in \mathbb N$ with $M_k > 0$ (hMk) and an embedding $\mathrm{selection} : \mathrm{Fin}\,\mathrm{dim} \hookrightarrow G$ with `GoodScalarKernelTuple selection (1/Mk) Mk x` (hx); a finite type $X$ and $\mathrm{stride} : X \to \mathbb N$; $q =$ `canonicalSlicedModulus selection stride m x` with $M = M_k$ (hqcanonical); $\mathrm{period} =$ `kernelPeriodCandidate (m+1) (goodKernelUniformCandidate selection x hx m)` (hperiodcanonical); and $y_0$ of positive weight under `containedSupportedProgressionLaw … H step c … hH hsubset q λ hcell` (hy₀). Write gridLaw $=$ `containedSupportedProgressionAxisLaw … H step c … hH hsubset q λ hcell grid`, ideal $=$ `allocatedRowSlicedIdeal B U b S rowSets ρ center width`, and invN $=$ `allocatedProductIdealNormalizer B U b S rowSets`$^{-1}$.
--
--   Assume further: $\mathrm{dim} \le m+1$; every $t \in \mathrm{rowSets}_j$ has $|t| \le j+1$; $\mathrm{period} \mid d$; $C_{\mathrm{fwd}} : \mathrm{Fin}\,m \to \mathbb R_{\ge 0}$ with $\|\texttt{normalizedOrthogonalChart …}\,v\| \le C_{\mathrm{fwd},j}\|v\|$; $K \in \mathbb R_{\ge 0}$ with $R_j^{-1} \le K$; $T : \mathrm{Fin}\,m \to \mathbb R$ with $T_j \ge 0$, `partitionedIdealRadius (Fin dim) m` $+1 \le T_j$, $|\texttt{BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j+1)}|\cdot 2^{\mathrm{dim}}(\mathrm{dim}+1)^{j+1} \le T_j$ and $|\mathrm{rowSets}_j|\,T_j \le r$; $\sigma_j \le 1$; $0 < \rho \le 1$ and $|\mathrm{center}(i)| + |\mathrm{width}(i)| \le 1$ for all $i$; reals $P_{\mathrm{box}}, P_\rho, V_{\log}, N_{\log}, M_{\log}, \mathrm{target} \ge 0$ with $2\cdot$`allocatedRowSlicedSiteRadius rowSets` $\le e^{P_{\mathrm{box}}}$, $\rho^{-1} \le e^{P_\rho}$, `allocatedFullGridNaturalVolume B U b S rowSets` $\le e^{V_{\log}}$, $\|\mathrm{invN}\| \le e^{N_{\log}}$, and `layerKernelIndexBound m Mk`$^{|\texttt{LayerSamplerAxis I n}|}\cdot$`coefficientDeckPeriodCap rowTypes E period` $\le e^{M_{\log}}$; and a real $\mathrm{base} \ge 0$ with $V_{\log}, N_{\log}, M_{\log} \le \mathrm{base}$, $2^{\mathrm{dim}} \le \mathrm{base}$, $|\texttt{LayerSamplerAxis I n}| \le \mathrm{base}$, $|\Sigma_a\,\mathrm{rowTypes}_{\mathrm{layer}(a)}| \le \mathrm{base}$, and each of $|(\prod_j(\mathbb Z/\mathrm{period})^{\mathrm{Fin}(n_j)})\times(\prod_j(\mathbb Z/\mathrm{period})^{E_j})|$, $K$, $\sum_j C_{\mathrm{fwd},j}|J_j|$, `normalizedSiteCutoffBound`, $d$, period, $\sum_j|\mathrm{rowSets}_j|$ and $S.\mathrm{value}^{\texttt{layerTailDegree m}+1}$ at most $e^{\mathrm{base}}$; and $1 \le r$.
--
--   Put $p = P_{\mathrm{box}} + P_\rho + V_{\log} + N_{\log} + M_{\log} + \mathrm{target}$, $Q =$ `idealSiteLogBudget` $(|\Sigma_a\,\mathrm{rowTypes}_{\mathrm{layer}(a)}|, \mathrm{dim}, p)$ and budget $=$ `affineAmbientPrimitiveBudget base Q` (a real number). Then there is $F : (\texttt{JetAmbientIndex rowTypes J} \to \mathbb R/\mathbb Z) \to \mathbb C$ (on the torus indexed by $\Sigma_j\,\mathrm{rowTypes}_j \times J_j$) that is $e^{\mathrm{budget}}$-Lipschitz, satisfies $\|F(z)\| \le e^{\mathrm{budget}}$ for all $z$, and for every $y$ in `EuclideanJetLayers U rowTypes`,
--   $$\Bigl\|\mathrm{gridLaw.mean}\bigl(u \mapsto \texttt{allocatedWholeMaskedCoveredProfile B U b hR hσ S x rows hb o bW d}\ (\texttt{principalAxisJoin grid u}\ (\texttt{principalAxisRestrict (¬ grid) y₀}))\ q\ \mathrm{ideal}\ y\bigr) - F(\texttt{coveredJetAmbientTorus U 1 y})\Bigr\| \le e^{-\mathrm{target}}.$$
--
--   Lean: `OAI.Erdos3.VectorPolynomial.exists_allocatedCanonicalSlice_bounded_ambient_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.exists_allocatedCanonicalSlice_bounded_ambient` (in `lean/OAI/Combinatorics/Progressions/Estimates/AllocatedCanonicalSliceConstructedModelSource.lean`); the definitions it uses are in the definitions bundles `OAIE3v2B216`, `OAIE3v2B217` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/AllocatedCanonicalSliceConstructedModelSource.lean (declaration OAI.Erdos3.VectorPolynomial.exists_allocatedCanonicalSlice_bounded_ambient)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B216
import Definitions.Def_OAIE3v2B217

section

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ}
variable (rowSets : Fin m → Finset (Finset (Fin dim)))

local notation "rowTypes" => (fun j : Fin m => {t : Finset (Fin dim) // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowTypes j → Finset (Fin dim)))
local notation "grid" => allocatedGridAxis (I := I) U b S.value

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
variable (q d period : ℕ) [NeZero d] [NeZero period]
variable (r : ℝ≥0) (hr : 0 < r)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

local notation "residue" => (fun j => integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
  (principalAxisRestrict grid y₀) rows j (principalAxisRestrict (fun a => ¬grid a) y₀)) q)
local notation "inverseNormalizer" => ((allocatedProductIdealNormalizer B U b S rowSets : ℝ) : ℂ)⁻¹

variable (hR : ∀ j, 0 < R j) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
variable (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
variable (hbudget : ∀ j, ((rowSets j).card + 1 : ℝ) * (Fintype.card (Finset (Fin dim)) *
  (C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)))) ≤ 1 / 4)

variable (ρ : ℝ≥0)
variable (center width : PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n)
  (α := Fin dim) (fun a => ¬allocatedGridAxis (I := I) U b S.value a) → ℝ)

variable (hσ : ∀ j, 0 < σ j)
variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ j, 0 < H j)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U b S j : ℤ))
variable (label : PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n) H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = label)))
local notation "gridLaw" => containedSupportedProgressionAxisLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) H step c (allocatedPrincipalSides_pos B U b S) hH hsubset q label hcell grid
local notation "ideal" => allocatedRowSlicedIdeal B U b S rowSets ρ center width

variable {Mk : ℕ} (hMk : 0 < Mk) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (Mk : ℝ)) Mk x)
variable {X : Type*} [Fintype X] (stride : X → ℕ)
variable (hqcanonical : q = canonicalSlicedModulus (M := Mk) selection stride m x)
variable (hperiodcanonical : period = kernelPeriodCandidate (m + 1) (goodKernelUniformCandidate selection x hx m))
variable (hy₀ : 0 < (containedSupportedProgressionLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) H step c (allocatedPrincipalSides_pos B U b S) hH hsubset q label hcell).weight y₀)

include hr hR hC hchart hbudget hMk hx hqcanonical hperiodcanonical hy₀ in
theorem exists_allocatedCanonicalSlice_bounded_ambient_s2
    (hdim : dim ≤ m + 1)
    (hrowDegree : ∀ j (t : rowSets j), t.val.card ≤ j.val + 1)
    (hdiv : period ∣ d)
    (Cforward : Fin m → ℝ≥0)
    (hforward : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) v‖ ≤ Cforward j * ‖v‖)
    (K : ℝ≥0) (hK : ∀ j, (R j)⁻¹ ≤ K)
    (T : Fin m → ℝ) (hT : ∀ j, 0 ≤ T j)
    (hTideal : ∀ j, partitionedIdealRadius (Fin dim) m + 1 ≤ T j)
    (hsource : ∀ j, (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
      ((2 : ℝ) ^ Fintype.card (Fin dim) * ((Fintype.card (Fin dim) : ℝ) + 1) ^ (j.val + 1)) ≤ T j)
    (hradius : ∀ j, (rowSets j).card * T j ≤ (r : ℝ)) (hσ1 : ∀ j, σ j ≤ 1)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hw : ∀ i, |center i| + |width i| ≤ 1)
    {Pbox Prho Vlog Nlog Mlog target : ℝ}
    (hPbox : 0 ≤ Pbox) (hPrho : 0 ≤ Prho) (hVlog : 0 ≤ Vlog)
    (hNlog : 0 ≤ Nlog) (hMlog : 0 ≤ Mlog) (htarget : 0 ≤ target)
    (hbox : 2 * (allocatedRowSlicedSiteRadius rowSets : ℝ) ≤ Real.exp Pbox)
    (hρp : (ρ : ℝ)⁻¹ ≤ Real.exp Prho)
    (hvolume : allocatedFullGridNaturalVolume B U b S rowSets ≤ Real.exp Vlog)
    (hnormalizer : ‖inverseNormalizer‖ ≤ Real.exp Nlog)
    (hmask : (layerKernelIndexBound m Mk : ℝ) ^ Fintype.card (LayerSamplerAxis I n) * coefficientDeckPeriodCap rowTypes E period ≤ Real.exp Mlog)
    {base : ℝ} (hbase : 0 ≤ base)
    (hvbase : Vlog ≤ base) (hnbase : Nlog ≤ base) (hmbase : Mlog ≤ base)
    (hsites : (Fintype.card (Finset (Fin dim)) : ℝ) ≤ base)
    (haxes : (Fintype.card (LayerSamplerAxis I n) : ℝ) ≤ base)
    (hlabels : (Fintype.card ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)) : ℝ) ≤ Real.exp base)
    (hKbase : (K : ℝ) ≤ Real.exp base)
    (hcoords : ((∑ j, Cforward j * Fintype.card (J j) : ℝ≥0) : ℝ) ≤ Real.exp base)
    (hcutoff : (normalizedSiteCutoffBound : ℝ) ≤ Real.exp base)
    (hrone : 1 ≤ r) (hdbase : (d : ℝ) ≤ Real.exp base) (hpbase : (period : ℝ) ≤ Real.exp base)
    (hrows : ((∑ j : Fin m, ((rowSets j).card : ℝ≥0) : ℝ≥0) : ℝ) ≤ Real.exp base)
    (houtputs : (Fintype.card (Σ a : LayerSamplerAxis I n, rowTypes a.1) : ℝ) ≤ base)
    (hheight : (S.value : ℝ) ^ (layerTailDegree m + 1) ≤ Real.exp base) :
    let p := Pbox + Prho + Vlog + Nlog + Mlog + target
    let Q := idealSiteLogBudget (Fintype.card (Σ a : LayerSamplerAxis I n, rowTypes a.1)) (Fintype.card (Fin dim)) p
    let budget := affineAmbientPrimitiveBudget base Q
    ∃ F : (JetAmbientIndex rowTypes J → UnitAddCircle) → ℂ,
      LipschitzWith ⟨Real.exp budget, Real.exp_nonneg _⟩ F ∧
      (∀ z, ‖F z‖ ≤ Real.exp budget) ∧
      ∀ y : EuclideanJetLayers U rowTypes,
        ‖((gridLaw).mean (fun u => allocatedWholeMaskedCoveredProfile B U b hR hσ S x rows hb o bW d
          (principalAxisJoin grid u (principalAxisRestrict (fun a => ¬grid a) y₀)) q ideal y) : ℂ) -
          F (coveredJetAmbientTorus U 1 y)‖ ≤ Real.exp (-target) := by
  sorry

end Erdos3.VectorPolynomial

end

end OAI
end
