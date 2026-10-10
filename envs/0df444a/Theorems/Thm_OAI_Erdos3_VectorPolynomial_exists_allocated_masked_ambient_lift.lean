-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_exists_allocated_masked_ambient_lift
-- name    : OAI.Erdos3.VectorPolynomial.exists_allocated_masked_ambient_lift
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-10T00:48:01.049013+00:00
-- url     : https://prove2.me/theorems/96474911-581d-479d-ae10-12e076730274
-- title:
--   The masked site chart factor lifts to a Lipschitz function on the ambient torus
-- statement:
--   Fix $m \in \mathbb N$, a finite type $G$, finite types $I_j$ ($j \in \mathrm{Fin}\,m$), $n : \mathrm{Fin}\,m \to \mathbb N$, finite types $B_a$ indexed by $a \in$ `LayerSamplerAxis I n` (the sigma type $\Sigma_j\, I_j \oplus \mathrm{Fin}(n_j)$; write $N_{\mathrm{ax}}$ for its cardinality), finite types $J_j$ with subspaces $U_j \le \mathbb R^{J_j}$, bases $b_j$ (indexed by $\mathrm{Fin}(n_j)$) of the orthogonal complement of `euclideanSubspace (U j)`, reals $R_j, \sigma_j$, a `LayerSamplerScale` $S$ (a structure bundling a positive natural number $S.\mathrm{value}$ with width and gap inequalities), orthonormal bases $o_j$ of `euclideanSubspace (U j)` indexed by $I_j$, and assume ($h_b$) that the $\mathbb Z$-span of the range of $b_j$ is `projectedIntegerLattice (euclideanSubspace (U j))` for every $j$. Let $E_j$ be finite types, $bW_j$ a $\mathbb Z$-basis indexed by $E_j$ of `latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))` (the integer lattice intersected with that subspace), $d \ne 0$ a natural number, $r > 0$ a nonnegative real, and $\mathrm{period} \ne 0$ a natural number. Write $\chi_j$ for the continuous linear equivalence `normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)`. Assume $\mathrm{period} \mid d$ and $R_j > 0$ for all $j$; let $C_j \ge 0$ be reals with $\|\chi_j^{-1}(v)\| \le C_j\|v\|$ for all $v$ and $C_j\bigl((|I_j|+1)(2 r R_j)\bigr) \le 1/4$; let $C^{\mathrm{fw}}_j \ge 0$ with $\|\chi_j(v)\| \le C^{\mathrm{fw}}_j\|v\|$ for all $v$; let $K \ge 0$ with $R_j^{-1} \le K$ for all $j$; let label be a pair of families (elements of $(\mathbb Z/\mathrm{period})^{\mathrm{Fin}(n_j)}$ and $(\mathbb Z/\mathrm{period})^{E_j}$ for each $j$); and let $f : \mathbb R^{\texttt{LayerSamplerAxis I n}} \to \mathbb C$ be $L$-Lipschitz (for some $L \ge 0$) with $\|f(z)\| \le 1$ for all $z$. Put $L_{\mathrm{coord}} = K\sum_j C^{\mathrm{fw}}_j\,|J_j|$, $L_{\mathrm{cut}} = \bigl(N_{\mathrm{ax}} \cdot \texttt{normalizedSiteCutoffBound}/(2r)\bigr) L_{\mathrm{coord}}$ (`normalizedSiteCutoffBound` is a constant chosen by OpenAI), and $L_{\mathrm{out}} = L_{\mathrm{cut}}\,d + \max(L\,L_{\mathrm{coord}}\,\mathrm{period},\ 4\,\mathrm{period}) \cdot \lfloor d/\mathrm{period} \rfloor$ (all nonnegative reals). Then there is $F : (\mathbb R/\mathbb Z)^{\Sigma_j\, \mathrm{Unit} \times J_j} \to \mathbb C$ that is $L_{\mathrm{out}}$-Lipschitz, satisfies $\|F(z)\| \le 1$ for all $z$, and for every $y \in$ `EuclideanJetLayers U (fun _ => Unit)` (one point of each quotient of `euclideanSubspace (U j)` by its integer lattice section),
--   $$\texttt{allocatedMaskedSiteChartFactor}\ B\ U\ b\ S\ o\ h_b\ bW\ d\ r\ h_r\ \mathrm{period}\ \mathrm{label}\ f\ y = 2\,F(\texttt{coveredJetAmbientTorus}\ U\ 1\ y).$$
--
--   Lean: `OAI.Erdos3.VectorPolynomial.exists_allocated_masked_ambient_lift` in `lean/OAI/Combinatorics/Progressions/Estimates/AllocatedFiniteModelPhysicalExpansion.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B054`, `OAIErdos3B152` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/AllocatedFiniteModelPhysicalExpansion.lean#L226

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B054
import Definitions.Def_OAIErdos3B152

namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped Classical BigOperators NNReal

variable {m : ℕ} {O J : Fin m → Type*}
variable [∀ j, Fintype (O j)] [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d] (r : ℝ≥0) (hr : 0 < r) (period : ℕ) [NeZero period]

local notation "single" => (fun _ : Fin m => Unit)
local notation "ambient" => JetAmbientIndex single J
local notation "chart" => mixedCoveredJetChart (O := single) U o b hb bW d
local notation "region" => mixedCoveredJetRegion (O := single) (E := E) U o b d
  (fun j (_ : Unit) => standardLatticeClosedQuarterBox (J j))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d] (r : ℝ≥0) (hr : 0 < r) (period : ℕ) [NeZero period]

local notation "single" => (fun _ : Fin m => Unit)
local notation "ambient" => JetAmbientIndex single J
local notation "chart" => mixedCoveredJetChart (O := single) U o b hb bW d
local notation "region" => mixedCoveredJetRegion (O := single) (E := E) U o b d
  (fun j (_ : Unit) => standardLatticeClosedQuarterBox (J j))

theorem exists_allocated_masked_ambient_lift
    (hdiv : period ∣ d)
    (hR : ∀ j, 0 < R j) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (hbudget : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)) ≤ 1 / 4)
    (Cforward : Fin m → ℝ≥0)
    (hforward : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) v‖ ≤ Cforward j * ‖v‖)
    (K : ℝ≥0) (hK : ∀ j, (R j)⁻¹ ≤ K)
    (label : (∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period))
    (f : (LayerSamplerAxis I n → ℝ) → ℂ) {L : ℝ≥0}
    (hf : LipschitzWith L f) (hf1 : ∀ z, ‖f z‖ ≤ 1) :
    let Lcoord := K * ∑ j, Cforward j * Fintype.card (J j)
    let Lcut := (Fintype.card (LayerSamplerAxis I n) * normalizedSiteCutoffBound / (2 * r)) * Lcoord
    let Lout := Lcut * d + max (L * Lcoord * period) (4 * period) * (d / period : ℕ)
    ∃ F : (ambient → UnitAddCircle) → ℂ,
      LipschitzWith Lout F ∧ (∀ z, ‖F z‖ ≤ 1) ∧
      ∀ y : EuclideanJetLayers U single,
        allocatedMaskedSiteChartFactor B U b S o hb bW d r hr period label f y =
          2 * F (coveredJetAmbientTorus U 1 y) := by
  sorry

end Erdos3.VectorPolynomial
end
end OAI
