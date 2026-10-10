-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_exists_allocatedSupportedSliced_natural_grid_site_expansion
-- name    : OAI.Erdos3.VectorPolynomial.exists_allocatedSupportedSliced_natural_grid_site_expansion
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-10T05:36:20.412271+00:00
-- url     : https://prove2.me/theorems/0f835085-813a-41d7-8b97-78c2be9d67b2
-- title:
--   A site expansion with exponential bounds approximates the grid PMF at the grid scale
-- statement:
--   Fix the section data: a natural number $m$; a finite type $G$; finite types $I_j$ with decidable equality and natural numbers $n_j$ ($j \in \mathrm{Fin}\,m$); finite types $B_a$ with decidable equality over the axes $a$ of `LayerSamplerAxis I n` (the sigma type $\Sigma_j\, I_j \oplus \mathrm{Fin}(n_j)$); finite types $J_j$, real subspaces $U_j \subseteq \mathbb R^{J_j}$ and bases `basis j` (indexed by $\mathrm{Fin}\,n_j$) of the orthogonal complements of `euclideanSubspace (U j)`; real functions $R, \sigma$ on $\mathrm{Fin}\,m$ with $R_j > 0$ (hR) and $\sigma_j > 0$ (hσ); a `LayerSamplerScale` $S$ (a structure bundling a positive natural number $S.\mathrm{value}$ with width and gap inequalities); a finite type $\alpha$ with decidable equality; $q \in \mathbb N$ with $q > 0$ (hq) and $r : \mathrm{FullInput} \to \mathrm{Option}\,\alpha \to \mathbb Z/q$, where FullInput $=$ `PrincipalTupleIndex B (layerSamplerDegree I n)`; $H, \mathrm{step} : \mathrm{FullInput} \to \mathbb N$ and $c : \mathrm{FullInput} \to \mathbb Z$ with $H_t > 0$ (hH) and each progression `integerProgressionSupport (c t) (step t) (H t)` $= \{c_t + \mathrm{step}_t k : 0 \le k < H_t\}$ contained in $[0,$ `allocatedPrincipalSides B U basis S t`$)$ (hsubset); the residue cell $\{y : \texttt{principalResidueLabel q y} = r\}$ of positive mass under `principalTupleWeights B (layerSamplerDegree I n) H hH` (hcell); and a layer $j$ with an index $i \in \mathrm{Fin}(n_j)$. Write degree $= j+1$.
--
--   Assume the axis $\langle j, \mathrm{inr}\,i\rangle$ satisfies `allocatedGridAxis U basis S.value` (hgrid); let $\delta > 0$ with $\delta\cdot$`allocatedPrincipalSides B U basis S ⟨⟨j, inr i⟩, b, v⟩` $\le H_{\langle j,\mathrm{inr}\,i\rangle,b,v}$ for all $b, v$; let $T \in \mathbb N$ with $(|\alpha|+1)q/\delta \le T$; assume $\mathrm{step}_{\langle j,\mathrm{inr}\,i\rangle,b,v} > 0$ for all $b, v$; let $A \in \mathbb R_{\ge 0}$ with `Real.smoothTransition` $A$-Lipschitz; let $P \ge 1$ with `scalarCubePrimitiveEnvelope Empty A 16 (128 * probabilityProfileLipschitz) 1` $\le P$, `scalarCubePrimitiveEnvelope α A 1 0 q` $\le P$ and $\mathrm{step}_{\langle j,\mathrm{inr}\,i\rangle,b,v}\, q \le P$ for all $b, v$; let rows be a finset of finsets of $\alpha$, each of cardinality at most degree, with `positiveModerateSpectrumBlockCount j |rows| ((layerTailDegree m + 1)|rows|)` $\le |B_{\langle j,\mathrm{inr}\,i\rangle}|$ and `uniformSpectrumBlockCount j |rows| (degree·|rows|)` $\le |B_{\langle j,\mathrm{inr}\,i\rangle}|$. Let $D, v, w, t, p_0, E, \varepsilon$ be reals with $D, v, w, t, p_0, E \ge 0$; $|\alpha| \le D$, $\mathrm{degree} \le D$, $|\mathrm{rows}| \le D$, `layerTailDegree m` $+1 \le D$, $|B_{\langle j,\mathrm{inr}\,i\rangle}| \le D$; $R_j \le e^v$, $R_j^{-1} \le e^v$; $\delta^{-1} \le e^w$; $T \le e^t$; $|\texttt{BoundedCoefficientExponent (LayerSamplerVariables G I n B) degree}| \le e^v$; $P \le e^{p_0}$; $0 < \varepsilon \le 1$ with $\varepsilon^{-1} \le e^E$; and $\sigma_j \le 1$. Put $p = $ `slicedGridGeometryLog D v w t` $+ p_0$, $E' = E + D(v+1) + 1$, $Q =$ `slicedGridSiteLog j |rows| ((layerTailDegree m + 1)|rows|) (degree·|rows|) D p E'`, and $O =$ `siteExponentialOutputLog (2^|α|) Q` $+ (D+1)(v+1)$.
--
--   Then there exists a `ScalarSiteExpansion` $e$ on $\mathrm{Finset}\,\alpha$ (a finite family of terms $k$, each with a period $p_k$, a coefficient $a_k \in \mathbb C$ and factors $\phi_{k,s} : \mathbb Z/p_k \times \mathbb R \to \mathbb C$; its integer evaluation at height $N$ is $y \mapsto \sum_k a_k \prod_s \phi_{k,s}(y_s \bmod p_k, y_s/N)$) such that:
--
--   - `e.Bounds` $(e^O, e^O, e^O, e^O, \exp(\texttt{slicedGridGeometryLog D v w t} + D + v + 8))$ holds: at most $e^O$ terms, periods in $(0, e^O]$, $\sum_k |a_k| \le e^O$, every factor of norm at most $1$ and $e^O$-Lipschitz in its real argument, and every factor vanishing at real arguments $x$ with $|x| \ge \exp(\texttt{slicedGridGeometryLog D v w t} + D + v + 8)$; and
--   - for every $x : G \to$ `IntegerScalarCubeBox α S.value` and every $y : \mathrm{Finset}\,\alpha \to \mathbb Z$ whose Möbius coefficients `booleanCoefficient y t` $= \sum_{u \subseteq t}(-1)^{|t\setminus u|}y(u)$ vanish for all $t \notin \mathrm{rows}$, with $N =$ `allocatedPrincipalGridScale B U basis j i` (a natural number),
--   $$\Bigl\| N^{|\mathrm{rows}|}\cdot \texttt{allocatedSupportedSlicedPhysicalGridPMF B U basis hR hσ S q r H step c hH hsubset hcell j i rows x}\,(t \mapsto \texttt{booleanCoefficient y t}) - \texttt{e.integerEval}\ N\ y \Bigr\| \le \varepsilon.$$
--
--   Lean: `OAI.Erdos3.VectorPolynomial.exists_allocatedSupportedSliced_natural_grid_site_expansion` in `lean/OAI/Combinatorics/Progressions/Sampling/AllocatedSupportedSlicedFullGridSite.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B055`, `OAIErdos3B145` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Sampling/AllocatedSupportedSlicedFullGridSite.lean#L609

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B055
import Definitions.Def_OAIErdos3B145

namespace OAI

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

local notation "height" => basisAxisScale (basis j) i
local notation "degree" => Fin.val j + 1
local notation "gamma" => principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i))
local notation "denom" => inactiveDenominator gamma
local notation "side" => inactiveSideLength degree height denom
local notation "cost" => (denom : ℝ) * 2 ^ degree
local notation "torusA" => blockTorusFactor (Fintype.card α) degree (Fintype.card (B (Sigma.mk j (Sum.inr i)))) (4 * gamma)
local notation "torusI" => blockTorusFactor (Fintype.card α) degree (Fintype.card (B (Sigma.mk j (Sum.inr i)))) 1

end Erdos3.VectorPolynomial

end

section

namespace Erdos3
open scoped NNReal

end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open scoped Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable (R : Fin m → ℝ) (j : Fin m) (i : Fin (n j))
variable (α : Type*) [Fintype α] (d T : ℕ)
local notation "degree" => Fin.val j + 1

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

local notation "height" => basisAxisScale (basis j) i
local notation "degree" => Fin.val j + 1
local notation "gamma" => principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i))
local notation "denom" => inactiveDenominator gamma
local notation "side" => inactiveSideLength degree height denom
local notation "cost" => (denom : ℝ) * 2 ^ degree
local notation "torusA" => blockTorusFactor (Fintype.card α) degree (Fintype.card (B (Sigma.mk j (Sum.inr i)))) (4 * gamma)
local notation "torusI" => blockTorusFactor (Fintype.card α) degree (Fintype.card (B (Sigma.mk j (Sum.inr i)))) 1

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

local notation "height" => basisAxisScale (basis j) i
local notation "degree" => Fin.val j + 1
local notation "gamma" => principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i))
local notation "denom" => inactiveDenominator gamma
local notation "side" => inactiveSideLength degree height denom
local notation "cost" => (denom : ℝ) * 2 ^ degree
local notation "torusA" => blockTorusFactor (Fintype.card α) degree (Fintype.card (B (Sigma.mk j (Sum.inr i)))) (4 * gamma)
local notation "torusI" => blockTorusFactor (Fintype.card α) degree (Fintype.card (B (Sigma.mk j (Sum.inr i)))) 1

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

local notation "height" => basisAxisScale (basis j) i
local notation "degree" => Fin.val j + 1
local notation "gamma" => principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i))
local notation "denom" => inactiveDenominator gamma
local notation "side" => inactiveSideLength degree height denom
local notation "cost" => (denom : ℝ) * 2 ^ degree
local notation "torusA" => blockTorusFactor (Fintype.card α) degree (Fintype.card (B (Sigma.mk j (Sum.inr i)))) (4 * gamma)
local notation "torusI" => blockTorusFactor (Fintype.card α) degree (Fintype.card (B (Sigma.mk j (Sum.inr i)))) 1

include hq in
theorem exists_allocatedSupportedSliced_natural_grid_site_expansion
    (hgrid : allocatedGridAxis (I := I) U basis S.value ⟨j,Sum.inr i⟩)
    {δ : ℝ} (hδ : 0 < δ)
    (hdense : ∀ b v, δ * allocatedPrincipalSides B U basis S ⟨⟨j,Sum.inr i⟩,b,v⟩ ≤
      (H ⟨⟨j,Sum.inr i⟩,b,v⟩ : ℝ))
    (T : ℕ) (hQT : (((Fintype.card α + 1) * q : ℕ) : ℝ) / δ ≤ T)
    (hstep : ∀ b v, 0 < step ⟨⟨j,Sum.inr i⟩,b,v⟩)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) (P : ℝ) (hP : 1 ≤ P)
    (hcP : scalarCubePrimitiveEnvelope Empty A 16 (128 * probabilityProfileLipschitz) 1 ≤ P)
    (hsP : scalarCubePrimitiveEnvelope α A 1 0 q ≤ P)
    (hstride : ∀ b v, ((step ⟨⟨j,Sum.inr i⟩,b,v⟩ * q : ℕ) : ℝ) ≤ P)
    (rows : Finset (Finset α)) (hrows : ∀ t ∈ rows, t.card ≤ degree)
    (hBa : positiveModerateSpectrumBlockCount j.val rows.card
      ((layerTailDegree m + 1) * rows.card) ≤ Fintype.card (B ⟨j,Sum.inr i⟩))
    (hBi : uniformSpectrumBlockCount j.val rows.card (degree * rows.card) ≤ Fintype.card (B ⟨j,Sum.inr i⟩))
    {D v w t p₀ E ε : ℝ}
    (hD : 0 ≤ D) (hv : 0 ≤ v) (hw : 0 ≤ w) (ht : 0 ≤ t) (hp₀ : 0 ≤ p₀) (hE : 0 ≤ E)
    (hcube : (Fintype.card α : ℝ) ≤ D) (hdegree : ((degree : ℕ) : ℝ) ≤ D)
    (hrowsD : (rows.card : ℝ) ≤ D) (htail : ((layerTailDegree m + 1 : ℕ) : ℝ) ≤ D)
    (hblocks : (Fintype.card (B ⟨j, Sum.inr i⟩) : ℝ) ≤ D)
    (hRv : R j ≤ Real.exp v) (hRi : (R j)⁻¹ ≤ Real.exp v)
    (hδw : δ⁻¹ ≤ Real.exp w) (hT : (T : ℝ) ≤ Real.exp t)
    (hcoeff : (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) degree) : ℝ) ≤ Real.exp v)
    (hPp₀ : P ≤ Real.exp p₀)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hεE : ε⁻¹ ≤ Real.exp E) (hσ1 : σ j ≤ 1) :
    let p := slicedGridGeometryLog D v w t + p₀
    let E' := E + D * (v + 1) + 1
    let Q := slicedGridSiteLog j.val rows.card ((layerTailDegree m + 1) * rows.card)
      (degree * rows.card) D p E'
    let O := siteExponentialOutputLog (Fintype.card (Finset α)) Q + (D + 1) * (v + 1)
    ∃ e : ScalarSiteExpansion.{uα,uα} (Finset α),
      e.Bounds (Real.exp O) (Real.exp O) (Real.exp O)
        ⟨Real.exp O, Real.exp_nonneg _⟩ (Real.exp (slicedGridGeometryLog D v w t + (D + v + 8))) ∧
      ∀ (x : G → IntegerScalarCubeBox α S.value) (y : Finset α → ℤ),
        (∀ t ∉ rows, booleanCoefficient y t = 0) →
        ‖(((allocatedPrincipalGridScale (G := G) B U basis (R := R) j i : ℝ) ^ rows.card *
          (allocatedSupportedSlicedPhysicalGridPMF B U basis hR hσ S q r H step c hH hsubset hcell j i rows x
            (fun t => booleanCoefficient y t)).toReal : ℝ) : ℂ) -
          e.integerEval (allocatedPrincipalGridScale (G := G) B U basis (R := R) j i) y‖ ≤ ε := by
  sorry

end Erdos3.VectorPolynomial
end
end OAI
