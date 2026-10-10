-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_exists_allocatedSupportedSliced_bounded_grid_site_expansion
-- name    : OAI.Erdos3.VectorPolynomial.exists_allocatedSupportedSliced_bounded_grid_site_expansion
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-10T05:49:22.226499+00:00
-- url     : https://prove2.me/theorems/150eafae-21b3-4e8b-9660-c36057d4d93a
-- title:
--   A bounded site expansion approximates the supported sliced grid PMF on a grid axis
-- statement:
--   Fix the section data: a natural number $m$; a finite type $G$; finite types $I_j$ with decidable equality and natural numbers $n_j$ ($j \in \mathrm{Fin}\,m$); finite types $B_a$ with decidable equality over the axes $a$ of `LayerSamplerAxis I n` (the sigma type $\Sigma_j\, I_j \oplus \mathrm{Fin}(n_j)$); finite types $J_j$, real subspaces $U_j \subseteq \mathbb R^{J_j}$ and bases `basis j` (indexed by $\mathrm{Fin}\,n_j$) of the orthogonal complements of `euclideanSubspace (U j)`; real functions $R, \sigma$ on $\mathrm{Fin}\,m$ with $R_j > 0$ (hR) and $\sigma_j > 0$ (hσ); a `LayerSamplerScale` $S$ (a structure bundling a positive natural number $S.\mathrm{value}$ with width and gap inequalities); a finite type $\alpha$ with decidable equality; $q \in \mathbb N$ and $r : \mathrm{FullInput} \to \mathrm{Option}\,\alpha \to \mathbb Z/q$, where FullInput $=$ `PrincipalTupleIndex B (layerSamplerDegree I n)`; $H, \mathrm{step} : \mathrm{FullInput} \to \mathbb N$ and $c : \mathrm{FullInput} \to \mathbb Z$ with $H_t > 0$ (hH) and each progression `integerProgressionSupport (c t) (step t) (H t)` $= \{c_t + \mathrm{step}_t k : 0 \le k < H_t\}$ contained in $[0,$ `allocatedPrincipalSides B U basis S t`$)$ (hsubset); the residue cell $\{y : \texttt{principalResidueLabel q y} = r\}$ of positive mass under `principalTupleWeights B (layerSamplerDegree I n) H hH` (hcell); and a layer $j \in \mathrm{Fin}\,m$ with an index $i \in \mathrm{Fin}(n_j)$. Write height $=$ `basisAxisScale (basis j) i` $= \lceil \|\mathrm{basis}_j(i)\|^{-1} \rceil$, Slots $=$ `BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j+1)`, and radius $= |\mathrm{Slots}| \cdot 2^{|\alpha|}(|\alpha|+1)^{j+1} R_j$.
--
--   Assume $\sigma_j \le 1$ and that the axis $\langle j, \mathrm{inr}\,i\rangle$ satisfies `allocatedGridAxis U basis S.value` (hgrid). Let rows be a finset of finsets of $\alpha$, $K_{\max} \in \mathbb N$ with height $\le K_{\max}$, and reals $\varepsilon > 0$, $P \ge 0$ with $|\mathrm{rows}|\cdot\mathrm{radius} + 1/4 \le e^P$, $K_{\max}^{|\mathrm{rows}|} \le e^P$, $|\mathrm{rows}| \cdot 2K_{\max}^2 \cdot K_{\max}^{|\mathrm{rows}|}\cdot 2^{|\alpha|} \le e^P$, and $\varepsilon^{-1} \le e^P$. Then there exists a `ScalarSiteExpansion` $e$ on $\mathrm{Finset}\,\alpha$ (a finite family of terms $k$, each with a period $p_k$, a coefficient $a_k \in \mathbb C$ and factors $\phi_{k,s} : \mathbb Z/p_k \times \mathbb R \to \mathbb C$ for $s \in \mathrm{Finset}\,\alpha$; its integer evaluation at height $N$ is $y \mapsto \sum_k a_k \prod_s \phi_{k,s}(y_s \bmod p_k, y_s/N)$) such that:
--
--   - `e.Bounds T 1 C L Hs` holds with $T = \exp(2^{|\alpha|}(4P+8))$, $C = \exp(2^{|\alpha|}(4P+8) + P)$, $L = \exp(1 + 6P + 12) + 4$ and $Hs = |\mathrm{rows}|\cdot\mathrm{radius} + 1/4$; that is, at most $T$ terms, all periods in $(0, 1]$, $\sum_k |a_k| \le C$, every factor of norm at most $1$ and $L$-Lipschitz in its real argument, and every factor vanishing at real arguments $x$ with $|x| \ge Hs$; and
--   - for every $x : G \to$ `IntegerScalarCubeBox α S.value` and every $y : \mathrm{Finset}\,\alpha \to \mathbb Z$ whose Möbius coefficients `booleanCoefficient y t` $= \sum_{u \subseteq t} (-1)^{|t \setminus u|} y(u)$ vanish for all $t \notin \mathrm{rows}$,
--   $$\Bigl\| \mathrm{height}^{|\mathrm{rows}|}\cdot \texttt{allocatedSupportedSlicedPhysicalGridPMF B U basis hR hσ S q r H step c hH hsubset hcell j i rows x}\,(t \mapsto \texttt{booleanCoefficient y t}) - \texttt{e.integerEval height y} \Bigr\| \le \varepsilon,$$
--   where the PMF (on $\mathrm{rows} \to \mathbb Z$) is the image of the layer integer PMF `allocatedLayerIntegerPMFs B U basis hR hσ S j i` under the bounded coefficient jet matrix at the physical cube root and directions, averaged over the conditioned law `containedSupportedProgressionLaw … H step c … hH hsubset q r hcell`.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.exists_allocatedSupportedSliced_bounded_grid_site_expansion` in `lean/OAI/Combinatorics/Progressions/Sampling/AllocatedSupportedSlicedInactiveGridSite.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B055`, `OAIErdos3B145` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Sampling/AllocatedSupportedSlicedInactiveGridSite.lean#L191

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B055
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

local notation "radius" => blockJetScaleBound (Fintype.card α) (Fin.val j + 1)
  (Fintype.card (B (Sigma.mk j (Sum.inr i)))) (4 * gamma)
local notation "height" => basisAxisScale (basis j) i
local notation "torus" => blockTorusFactor (Fintype.card α) (Fin.val j + 1)
  (Fintype.card (B (Sigma.mk j (Sum.inr i)))) (4 * gamma)

local notation "conditioned" => containedSupportedProgressionLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) H step c (allocatedPrincipalSides_pos B U basis S) hH hsubset q r hcell
local notation "constantLaw" => allocatedLayerIntegerPMFs B U basis hR hσ S j i
  (principalCoefficientChoice (G := G) (layerSamplerDegree I n) (Sigma.mk j (Sum.inr i)) none)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

universe uα

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
variable {α : Type uα} [Fintype α] [DecidableEq α]
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
local notation "constantLaw" => allocatedLayerIntegerPMFs B U basis hR hσ S j i
  (principalCoefficientChoice (G := G) (layerSamplerDegree I n) (Sigma.mk j (Sum.inr i)) none)

local notation "height" => basisAxisScale (basis j) i
local notation "degree" => Fin.val j + 1
local notation "Slots" => BoundedCoefficientExponent (LayerSamplerVariables G I n B) degree
local notation "radius" => (Fintype.card Slots : ℝ) *
  ((2 : ℝ) ^ Fintype.card α * ((Fintype.card α : ℝ) + 1) ^ degree) * R j

theorem exists_allocatedSupportedSliced_bounded_grid_site_expansion
    (hσ1 : σ j ≤ 1) (hgrid : allocatedGridAxis (I := I) U basis S.value ⟨j, Sum.inr i⟩)
    (rows : Finset (Finset α)) {Kmax : ℕ} (hKmax : height ≤ Kmax)
    {ε P : ℝ} (hε : 0 < ε) (hP : 0 ≤ P)
    (hHP : rows.card * radius + 1 / 4 ≤ Real.exp P)
    (hcap : (Kmax : ℝ) ^ rows.card ≤ Real.exp P)
    (hLip : ((rows.card * (2 * (Kmax : ℝ≥0) ^ 2) * (Kmax : ℝ≥0) ^ rows.card) *
      (2 : ℝ≥0) ^ Fintype.card α : ℝ≥0) ≤ Real.exp P)
    (hεP : ε⁻¹ ≤ Real.exp P) :
    ∃ e : ScalarSiteExpansion.{uα,uα} (Finset α),
      e.Bounds (Real.exp (Fintype.card (Finset α) * (4 * P + 8))) 1
        (Real.exp (Fintype.card (Finset α) * (4 * P + 8) + P))
        (⟨Real.exp (1 + 6 * P + 12), Real.exp_nonneg _⟩ + 4) (rows.card * radius + 1 / 4) ∧
      ∀ (x : G → IntegerScalarCubeBox α S.value) (y : Finset α → ℤ),
        (∀ t ∉ rows, booleanCoefficient y t = 0) →
        ‖(((height : ℝ) ^ rows.card *
          (allocatedSupportedSlicedPhysicalGridPMF B U basis hR hσ S q r H step c hH hsubset hcell j i rows x
            (fun t => booleanCoefficient y t)).toReal : ℝ) : ℂ) - e.integerEval height y‖ ≤ ε := by
  sorry

end Erdos3.VectorPolynomial
end
end OAI
