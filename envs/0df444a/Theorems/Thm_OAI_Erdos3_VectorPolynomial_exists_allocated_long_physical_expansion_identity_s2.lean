-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_exists_allocated_long_physical_expansion_identity_s2
-- name    : OAI.Erdos3.VectorPolynomial.exists_allocated_long_physical_expansion_identity_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T04:48:37.56851+00:00
-- url     : https://prove2.me/theorems/63a29229-412a-4f94-84e0-53cf75d58195
-- title:
--   The chart ideal approximation along physical cube samples expands into Lipschitz bounded factors on a long torus
-- statement:
--   All named objects below are defined by OpenAI.
--
--   **Setting.** Let $m$ be a natural number, $G$ a finite type, $I_j$ ($j<m$) finite types, $n : \mathrm{Fin}(m)\to\mathbb{N}$, $B_a$ finite types indexed by `LayerSamplerAxis I n` $= \Sigma_j (I_j \sqcup \mathrm{Fin}(n_j))$, $J_j$ finite types, $U_j \subseteq \mathbb{R}^{J_j}$ subspaces, `b j` bases (indexed by $\mathrm{Fin}(n_j)$) of the orthogonal complement of `euclideanSubspace (U j)`, $R, \sigma : \mathrm{Fin}(m) \to \mathbb{R}$, and `S : LayerSamplerScale B U b R σ`. Let $\mathrm{dim}$ be a natural number, $E_j$ finite types, $x : G \to$ `IntegerScalarCubeBox (Fin dim) S.value`, $y_0 \in$ `PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S)`, natural numbers $q$, $d \ge 1$, $\mathrm{period} \ge 1$, $r \in \mathbb{R}_{\ge 0}$ with $r > 0$, `hb` the statement that the $\mathbb{Z}$-span of each `b j` is the projected integer lattice, $o_j$ orthonormal bases of `euclideanSubspace (U j)` indexed by $I_j$, and `bW j` $\mathbb{Z}$-bases (indexed by $E_j$) of the lattice section of $\mathbb{Z}^{J_j}$ in `euclideanSubspace (U j)`.
--
--   **Hypotheses.** Assume: $\mathrm{period} \mid d$; $R_j > 0$ for all $j$; $C : \mathrm{Fin}(m)\to\mathbb{R}$ with $C_j \ge 0$ and $\|\Phi_j^{-1}(v)\| \le C_j\|v\|$ for all $j, v$, where $\Phi_j$ = `normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)`; $C_j\,((|I_j| + 1)(2rR_j)) \le 1/4$ for all $j$; $C^{\mathrm{fwd}} : \mathrm{Fin}(m) \to \mathbb{R}_{\ge 0}$ with $\|\Phi_j(v)\| \le C^{\mathrm{fwd}}_j\|v\|$ for all $j, v$; $K \in \mathbb{R}_{\ge 0}$ with $R_j^{-1} \le K$ for all $j$. Let $T$ be a finite type, $a : T \to \mathbb{C}$, and $f : T \to \mathrm{Finset}(\mathrm{Fin}\ \mathrm{dim}) \to (\texttt{LayerSamplerAxis I n} \to \mathbb{R}) \to \mathbb{C}$ with every $f_k(s)$ being $L$-Lipschitz (for some $L \in \mathbb{R}_{\ge 0}$) and bounded in norm by $1$. Let $X$ be a type and `p j : VectorPolynomial X ℝ (J j → ℝ)` vector polynomials of degree at most $j+1$ for the unit weight on $X$, with all coefficients in $U_j$ (hypothesis `hm`).
--
--   **Statement.** Let
--   $$L_{\mathrm{coord}} = K\sum_j C^{\mathrm{fwd}}_j\,|J_j|, \qquad L_{\mathrm{out}} = \frac{|\texttt{LayerSamplerAxis I n}|\cdot \texttt{normalizedSiteCutoffBound}}{2r}\, L_{\mathrm{coord}} + \max\bigl(L\, L_{\mathrm{coord}}\,\mathrm{period},\ 4\,\mathrm{period}\bigr),$$
--   where `normalizedSiteCutoffBound` $\ge 1$ is a constant chosen by OpenAI. Then there is a function $g$ which takes a label (a map from $\mathrm{Finset}(\mathrm{Fin}\ \mathrm{dim})$ to pairs of residue arrays $(\prod_j (\mathrm{Fin}(n_j) \to \mathbb{Z}/\mathrm{period})) \times (\prod_j (E_j \to \mathbb{Z}/\mathrm{period}))$), an index $k \in T$, and a subset $s \subseteq \mathrm{Fin}(\mathrm{dim})$, and returns a function from the long torus $(\texttt{JetAmbientIndex (fun _ => Unit) J} \to \mathbb{R}/\mathbb{Z}) \times ((\Sigma_j J_j) \to \mathbb{R}/\mathbb{Z})$ to $\mathbb{C}$, such that every $g(\mathrm{label}, k, s)$ is $L_{\mathrm{out}}$-Lipschitz, every $g(\mathrm{label}, k, s)$ has norm at most $1$ everywhere, and `AllocatedLongPhysicalExpansionIdentity B U b S x y₀ q d period r hr hb o bW a f p hm g` holds. The latter means: with `rowSets j` = `boundedBooleanJetRows (Fin dim) (j+1)` and `rows` its inclusion, for every integer array $v : X \to (\mathrm{Unit} \sqcup \mathrm{Fin}\ \mathrm{dim}) \to \mathbb{Z}$,
--   $$\texttt{allocatedProductChartIdealApproximation}\ \ldots\ a\ f\ \bigl(\texttt{physicalCubeRowSample U d rows p hm}\ v\bigr) = \sum_{\mathrm{label}}\sum_{i \in T} 2^{2^{\mathrm{dim}}}\, c(\mathrm{label}, i) \prod_{s} g(\mathrm{label}, i, s)\bigl(\texttt{physicalMaskedFactorInput period p}\ (z \mapsto \texttt{physicalCubeVertexValue}\ v\ s\ z)\bigr),$$
--   where $c(\mathrm{label}, i)$ = `allocatedProductMaskedIdealCoefficient B U b S rowSets x y₀ q d period a label i` and $2^{\mathrm{dim}} = |\mathrm{Finset}(\mathrm{Fin}\ \mathrm{dim})|$.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.exists_allocated_long_physical_expansion_identity_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.exists_allocated_long_physical_expansion_identity` (in `lean/OAI/Combinatorics/Progressions/Estimates/AllocatedFiniteModelPhysicalExpansion.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B216` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/AllocatedFiniteModelPhysicalExpansion.lean (declaration OAI.Erdos3.VectorPolynomial.exists_allocated_long_physical_expansion_identity)

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

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
variable (q d period : ℕ) [NeZero d] [NeZero period]
variable (r : ℝ≥0) (hr : 0 < r)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

attribute [local instance] ScalarSiteExpansion.termFinite
attribute [local instance 2000] fullGridCoverAxisDecidableEq

variable (e : {a // allocatedGridAxis (I := I) U b S.value a} → ScalarSiteExpansion.{0,0} (Finset (Fin dim)))

theorem exists_allocated_long_physical_expansion_identity_s2
    (hdiv : period ∣ d)
    (hR : ∀ j, 0 < R j) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (hbudget : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)) ≤ 1 / 4)
    (Cforward : Fin m → ℝ≥0)
    (hforward : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) v‖ ≤ Cforward j * ‖v‖)
    (K : ℝ≥0) (hK : ∀ j, (R j)⁻¹ ≤ K)
    {T : Type*} [Fintype T] (a : T → ℂ)
    (f : T → Finset (Fin dim) → (LayerSamplerAxis I n → ℝ) → ℂ) {L : ℝ≥0}
    (hf : ∀ k s, LipschitzWith L (f k s)) (hf1 : ∀ k s z, ‖f k s z‖ ≤ 1)
    {X : Type*} (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hm : ∀ j e, coefficients (p j) e ∈ U j) :
    let Lcoord := K * ∑ j, Cforward j * Fintype.card (J j)
    let Lout := (Fintype.card (LayerSamplerAxis I n) * normalizedSiteCutoffBound / (2 * r)) * Lcoord +
      max (L * Lcoord * period) (4 * period)
    ∃ g : (Finset (Fin dim) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period))) →
        T → Finset (Fin dim) →
        ((JetAmbientIndex (fun _ : Fin m => Unit) J → UnitAddCircle) × ((Σ j, J j) → UnitAddCircle)) → ℂ,
      (∀ label k s, LipschitzWith Lout (g label k s)) ∧
      (∀ label k s z, ‖g label k s z‖ ≤ 1) ∧
      AllocatedLongPhysicalExpansionIdentity B U b S x y₀ q d period r hr hb o bW a f p hm g := by
  sorry

end Erdos3.VectorPolynomial

end

end OAI
end
