-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedOriginalPathLaw_canonical_period_source_s2
-- name    : OAI.Erdos3.VectorPolynomial.allocatedOriginalPathLaw_canonical_period_source_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T04:57:34.629506+00:00
-- url     : https://prove2.me/theorems/534ecb64-9908-4fd8-8079-ca302a3de022
-- title:
--   A detected niltest slice gives a sliced source at the canonical refined period
-- statement:
--   Fix the section data: a natural number $m$; a finite type $G$ (in `Type`) with decidable equality; finite types $I_j$ with decidable equality and natural numbers $n_j$ ($j \in \mathrm{Fin}\,m$); finite types $B_a$ with decidable equality over the axes $a$ of `LayerSamplerAxis I n` ($= \Sigma_j\,(I_j \oplus \mathrm{Fin}\,n_j)$); finite types $J_j$, real subspaces $U_j \subseteq \mathbb R^{J_j}$, $V_j = $ `euclideanSubspace (U j)`, bases $b_j$ (indexed by $\mathrm{Fin}\,n_j$) of $V_j^\perp$ with $hb$: the $\mathbb Z$-span of $b_j$ is `projectedIntegerLattice V_j`; orthonormal bases $o_j$ of $V_j$ indexed by $I_j$; real functions $R, \sigma$ on $\mathrm{Fin}\,m$ with $R_j > 0$, $\sigma_j > 0$; a layer-sampler scale `S : LayerSamplerScale B U b R σ` with value $L_S = $ `S.value`; a natural number $s$; a finite type $X$; vector polynomials $\mathrm{poly}_j \in$ `VectorPolynomial X ℝ (J j → ℝ)` with all coefficients in $U_j$ ($hmem$); the assumption that each $\mathbb Z^{J_j} \cap V_j$ is a full lattice in $V_j$; $N : X \to \mathbb N$ with $N_t > 0$; reals $W \ge 0$, $\tau > 0$, $\xi > 0$; $\mathrm{stride} : X \to \mathbb N$; a finite set $\mathrm{cells}$ of `ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride`; with $\mathrm{widths} = $ `narrowTrimmedSpatialWidths W τ ξ N` (a real function on $\mathrm{Option}(\texttt{LayerSamplerVariables G I n B}) \times X$), $hmass$: $\sum_z$ `selectedResidueSmoothWeight stride cells widths z` $> 0$; a nonempty finite set $\mathrm{bases} \subseteq (X \to \mathbb Z)$; and $htotal$: `selectedJointDensityMass bases stride cells widths (allocatedJointBaseDensity B U b hb o hR hσ S X poly hmem)` $> 0$. Write sides for the function on $G \oplus$ (tuple index) equal to $L_S$ on $G$ and to `allocatedPrincipalSides B U b S` on tuple indices; Path for the type $\mathrm{bases} \times$ `rectangularWeightIndices 0 widths 1`; and pathLaw for `allocatedOriginalPathLaw B U b hb o hR hσ S X poly hmem N hN hW hτ hξ stride cells hmass bases hbases htotal`, a finite probability law on Path defined by OpenAI. Here `LayerSamplerVariables G I n B` is the index type $G \oplus$ (tuple index), the tuple index being `PrincipalTupleIndex B (layerSamplerDegree I n)`.
--
--   Let $P \in \mathbb N[t]$; $T$ a nonempty finite type with an injection $e : T \to (\texttt{LayerSamplerVariables G I n B} \to \mathbb Z)$; for each $z \in$ Path a nonempty type $\mathrm{Tests}_z$, and for each $j \in \mathrm{Tests}_z$ a Lie algebra $L_{z,j}$ over $\mathbb Q$ with a Hausdorff topological-vector-space structure on $\mathbb R \otimes_{\mathbb Q} L_{z,j}$, a natural number $\mathrm{dims}_{z,j}$, a `RationalFilteredNilmanifold (L z j) s (dims z j)` $D_{z,j}$ and a niltest $V_{z,j}$ on it (variables `LayerSamplerVariables G I n B`, weights $1$); finite sets $\mathrm{slices}_{z,j} \subseteq T$, $c_{z,j} : \texttt{LayerSamplerVariables G I n B} \to \mathbb Z$, natural numbers $\mathrm{step}_{z,j} > 0$ and $H_{z,j} : \texttt{LayerSamplerVariables G I n B} \to \mathbb N$ such that $e(\mathrm{slices}_{z,j}) = $ `commonStrideBox (c z j) (step z j) (H z j)` (the product of the progressions $\{c_i + \mathrm{step}\,k : 0 \le k < H_i\}$); reals $p, q \ge 0$ such that each $e(\mathrm{slices}_{z,j})$ is `IsDenseCommonStrideBox sides p` (a common-stride box inside $[0, \mathrm{sides})$ with every length $\ge e^{-p}\,\mathrm{sides}$), $|\texttt{LayerSamplerVariables G I n B}| \le P(q)$, each $V_{z,j}$ has complexity at most $P(q)$ and norm bound at most $1$; a function $f : (X \to \mathbb Z) \to \mathbb C$ with $\|f\| \le 1$; a real $\alpha$ with $0 < \alpha \le 1$, $|\texttt{LayerSamplerVariables G I n B}|\,e^{-p} \le \alpha/8$ and $e^{-q} \le \alpha/4$; and the detection hypothesis
--   $$\alpha \le \texttt{sampledSliceSeminorm}\ \mathrm{pathLaw}\ \bigl(z, t \mapsto \texttt{jointIntegerPhysicalSite}(e\,t)(z)\bigr)\ \mathrm{slices}\ \bigl(z, j, t \mapsto \overline{V_{z,j}(\texttt{commonStrideIndex}(c_{z,j}, \mathrm{step}_{z,j}, e\,t))}\bigr)\ (f),$$
--   a seminorm defined by OpenAI. Let $\mathrm{selection} : \mathrm{Fin}(s+1) \hookrightarrow G$ with $(s+1)(s+3) \le |G|$; put
--   $$\mathrm{gain} = e^{-((5p+20)\,|\texttt{LayerSamplerVariables G I n B}| + p + 2)}\,\frac{\alpha}{2}\cdot \bigl(e^{-(q + C_s)^{C_s}}\bigr)^{2^{s+1}},\qquad C_s = \texttt{sampledSupportedSlicedDetectionConstant}\ s\ P,$$
--   (a natural-number constant chosen by OpenAI) and $M_k = $ `scalarKernelCutoff (Fin (s+1)) G 1 ⌈exp(p+1)⌉ (gain/2)` (a natural number defined by OpenAI), and assume $M_k \le L_S$ and $\mathrm{stride}_i > 0$ for every $i \in X$.
--
--   Then there exist $c_0 : \texttt{LayerSamplerVariables G I n B} \to \mathbb Z$, a natural number $\mathrm{step}_0 > 0$ and $H_0 : \texttt{LayerSamplerVariables G I n B} \to \mathbb N$ with $H_0 > 0$, such that every progression $\{c_0(i) + \mathrm{step}_0 k : 0 \le k < H_0(i)\}$ lies in $[0, \mathrm{sides}_i)$, $e^{-(p+1)}\,\mathrm{sides}_i \le H_0(i)$, and $\mathrm{step}_0 \le 4e^{p+1}$; and there exist $x : G \to $ `IntegerScalarCubeBox (Fin (s+1)) L_S` and a proof $hx$ of `GoodScalarKernelTuple selection (1/Mk) Mk x` such that, with $\mathrm{period} = $ `kernelPeriodCandidate (m+1) (goodKernelUniformCandidate selection x hx m)` and $\mathrm{refined} = $ `residueRefinedPeriod period stride` $= \mathrm{period}\cdot\prod_{i \in X}\mathrm{stride}_i$, we have $0 < M_k$, $0 < \mathrm{period} \le M_k^{m+1}$, and there exist a label $r :$ tuple index $\to \mathrm{Option}(\mathrm{Fin}(s+1)) \to \mathbb Z/\mathrm{refined}$ with positive mass of the tuples with residue label $r$ under `principalTupleWeights B (layerSamplerDegree I n) (H₀ ∘ inr) _`, and a proof $hsubset$ that the progressions of $c_0, \mathrm{step}_0, H_0$ on the tuple indices lie in $[0, \texttt{allocatedPrincipalSides B U b S j})$, such that
--   $$\frac{\mathrm{gain}}{2} \le \mathrm{Re}\ \mathbb E_{y \sim \lambda}\ \texttt{allocatedSlicedTupleValue B U b hb o hR hσ S X poly hmem N hN hW hτ hξ stride cells hmass bases x y f},$$
--   where $\lambda = $ `containedSupportedProgressionLaw B (layerSamplerDegree I n) (allocatedPrincipalSides B U b S) (H₀ ∘ inr) (fun _ => step₀) (c₀ ∘ inr) _ _ hsubset refined r hr` (a finite probability law on integer tuples, with `complexMean` its expectation) and `allocatedSlicedTupleValue … x y f` is the complex value defined by OpenAI as a normalized average over $\mathrm{bases}$ and residue cells of a physical cube site test of $f$ weighted by the joint base density; and moreover there exists a tuple $y_0$ in `PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin (s+1)) (allocatedPrincipalSides B U b S)` with $\lambda(y_0) > 0$, with each $y_0(j)$ satisfying `IntegerScalarCube (allocatedPrincipalSides B U b S j)`, such that for every predicate $\mathrm{axis}$ on `LayerSamplerAxis I n` the restriction of $y_0$ to the axes satisfying it has positive weight under the corresponding `containedSupportedProgressionAxisLaw … refined r hr axis`, and every $y$ with $\lambda(y) \neq 0$ has the same residue label modulo $\mathrm{refined}$ (`principalResidueLabel refined`) as $y_0$.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.allocatedOriginalPathLaw_canonical_period_source_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.allocatedOriginalPathLaw_canonical_period_source` (in `lean/OAI/Combinatorics/Progressions/Estimates/AllocatedDetectedCanonicalPeriod.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B234` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/AllocatedDetectedCanonicalPeriod.lean (declaration OAI.Erdos3.VectorPolynomial.allocatedOriginalPathLaw_canonical_period_source)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B234

section

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical TensorProduct

variable {m : ℕ} {G : Type} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {s : ℕ} (X : Type) [Fintype X]
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j e, coefficients (poly j) e ∈ U j)

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

variable (N : X → ℕ) (hN : ∀ t, 0 < N t)
variable {W τ ξ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hξ : 0 < ξ)
variable (stride : X → ℕ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))

local notation "widths" => narrowTrimmedSpatialWidths (G := G)
  (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N

variable (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride cells
  (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N) z)
variable (bases : Finset (X → ℤ)) (hbases : bases.Nonempty)
variable (htotal : 0 < selectedJointDensityMass bases stride cells
  (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N)
  (allocatedJointBaseDensity B U b hb o hR hσ S X poly hmem))

local notation "sides" => Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U b S)

local notation "Path" => bases × rectangularWeightIndices 0 widths 1
local notation "pathLaw" => allocatedOriginalPathLaw B U b hb o hR hσ S X poly hmem
  N hN hW hτ hξ stride cells hmass bases hbases htotal

theorem allocatedOriginalPathLaw_canonical_period_source_s2
    (P : Polynomial ℕ)
    {T : Type} [Fintype T] [Nonempty T]
    (e : T → LayerSamplerVariables G I n B → ℤ) (he : Function.Injective e)
    {Tests : Path → Type} [∀ z, Nonempty (Tests z)]
    {L : ∀ z, Tests z → Type} [∀ z j, LieRing (L z j)] [∀ z j, LieAlgebra ℚ (L z j)]
    {dims : ∀ z, Tests z → ℕ}
    [∀ z j, TopologicalSpace (ℝ ⊗[ℚ] L z j)]
    [∀ z j, IsTopologicalAddGroup (ℝ ⊗[ℚ] L z j)]
    [∀ z j, ContinuousSMul ℝ (ℝ ⊗[ℚ] L z j)] [∀ z j, T2Space (ℝ ⊗[ℚ] L z j)]
    (D : ∀ z j, RationalFilteredNilmanifold (L z j) s (dims z j))
    (V : ∀ z j, (D z j).Niltest (fun _ : LayerSamplerVariables G I n B => 1))
    (slices : ∀ z, Tests z → Finset T)
    (c : ∀ z, Tests z → LayerSamplerVariables G I n B → ℤ)
    (step : ∀ z, Tests z → ℕ)
    (H : ∀ z, Tests z → LayerSamplerVariables G I n B → ℕ)
    (hstep : ∀ z j, 0 < step z j)
    (hslices : ∀ z j, (slices z j).image e = commonStrideBox (c z j) (step z j) (H z j))
    (p q : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hdense : ∀ z j, IsDenseCommonStrideBox sides p ((slices z j).image e))
    (hdimension : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P.eval₂ (Nat.castRingHom ℝ) q)
    (hcomplexity : ∀ z j, (V z j).ComplexityLE (P.eval₂ (Nat.castRingHom ℝ) q))
    (hcap : ∀ z j, ((V z j).normBound : ℝ) ≤ 1)
    (f : (X → ℤ) → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1)
    (α : ℝ) (hα : 0 < α) (hαone : α ≤ 1)
    (hmesh : Fintype.card (LayerSamplerVariables G I n B) * Real.exp (-p) ≤ α / 8)
    (hthreshold : Real.exp (-q) ≤ α / 4)
    (hdetected : α ≤ sampledSliceSeminorm (pathLaw)
      (fun z t => jointIntegerPhysicalSite (e t) (z.1.val, z.2.val)) slices
      (fun z j t => star ((V z j).eval (commonStrideIndex (c z j) (step z j) (e t)))) f)
    (selection : Fin (s + 1) ↪ G) (hG : (s + 1) * (s + 3) ≤ Fintype.card G)
    (hkernel : scalarKernelCutoff (Fin (s + 1)) G 1 ⌈Real.exp (p + 1)⌉₊
      (((Real.exp (-((5 * p + 20) * Fintype.card (LayerSamplerVariables G I n B) + p + 2)) * (α / 2)) *
        Real.exp (-((q + sampledSupportedSlicedDetectionConstant s P) ^ sampledSupportedSlicedDetectionConstant s P)) ^
          (2 ^ (s + 1))) / 2) ≤ S.value)
    (hstride : ∀ i, 0 < stride i) :
    let gain := (Real.exp (-((5 * p + 20) * Fintype.card (LayerSamplerVariables G I n B) + p + 2)) * (α / 2)) *
      Real.exp (-((q + sampledSupportedSlicedDetectionConstant s P) ^ sampledSupportedSlicedDetectionConstant s P)) ^
        (2 ^ (s + 1))
    let Mk := scalarKernelCutoff (Fin (s + 1)) G 1 ⌈Real.exp (p + 1)⌉₊ (gain / 2)
    ∃ (c₀ : LayerSamplerVariables G I n B → ℤ) (step₀ : ℕ)
      (H₀ : LayerSamplerVariables G I n B → ℕ) (_hstep₀ : 0 < step₀) (hH₀ : ∀ k, 0 < H₀ k),
      (∀ i, integerProgressionSupport (c₀ i) (step₀ : ℤ) (H₀ i) ⊆ Finset.Ico (0 : ℤ) (sides i : ℤ)) ∧
      (∀ i, Real.exp (-(p + 1)) * sides i ≤ (H₀ i : ℝ)) ∧
      (step₀ : ℝ) ≤ 4 * Real.exp (p + 1) ∧
    ∃ (x : G → IntegerScalarCubeBox (Fin (s + 1)) S.value),
      ∃ hx : GoodScalarKernelTuple selection (1 / (Mk : ℝ)) Mk x,
      let period := kernelPeriodCandidate (m + 1) (goodKernelUniformCandidate selection x hx m)
      0 < Mk ∧ 0 < period ∧ period ≤ Mk ^ (m + 1) ∧
    ∃ (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin (s + 1)) → ZMod (residueRefinedPeriod period stride))
      (hr : 0 < (principalTupleWeights (α := Fin (s + 1)) B (layerSamplerDegree I n)
        (fun j => H₀ (Sum.inr j)) (fun j => hH₀ (Sum.inr j))).mass
          (Finset.univ.filter (fun y => principalResidueLabel (residueRefinedPeriod period stride) y = r))),
      ∃ hsubset : ∀ j, integerProgressionSupport (c₀ (Sum.inr j)) (step₀ : ℤ) (H₀ (Sum.inr j)) ⊆
        Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U b S j : ℤ),
      let law := containedSupportedProgressionLaw B (layerSamplerDegree I n)
        (allocatedPrincipalSides B U b S) (fun j => H₀ (Sum.inr j)) (fun _ => step₀)
        (fun j => c₀ (Sum.inr j)) (allocatedPrincipalSides_pos B U b S)
        (fun j => hH₀ (Sum.inr j)) hsubset (residueRefinedPeriod period stride) r hr
      gain / 2 ≤ (law.complexMean (fun y => allocatedSlicedTupleValue B U b hb o hR hσ S X poly hmem
        N hN hW hτ hξ stride cells hmass bases x y f)).re ∧
      ∃ y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin (s + 1)) (allocatedPrincipalSides B U b S),
        0 < law.weight y₀ ∧
        (∀ j, IntegerScalarCube (allocatedPrincipalSides B U b S j) (fun a => (y₀ j a : ℤ))) ∧
        (∀ axis : LayerSamplerAxis I n → Prop,
          0 < (containedSupportedProgressionAxisLaw B (layerSamplerDegree I n)
            (allocatedPrincipalSides B U b S) (fun j => H₀ (Sum.inr j)) (fun _ => step₀)
            (fun j => c₀ (Sum.inr j)) (allocatedPrincipalSides_pos B U b S)
            (fun j => hH₀ (Sum.inr j)) hsubset (residueRefinedPeriod period stride) r hr axis).weight (principalAxisRestrict axis y₀)) ∧
        (∀ y, law.weight y ≠ 0 → principalResidueLabel (residueRefinedPeriod period stride) y = principalResidueLabel (residueRefinedPeriod period stride) y₀) := by
  sorry

end Erdos3.VectorPolynomial

end

end OAI
end
