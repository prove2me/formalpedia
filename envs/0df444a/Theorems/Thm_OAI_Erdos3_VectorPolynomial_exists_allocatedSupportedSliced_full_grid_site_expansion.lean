-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_exists_allocatedSupportedSliced_full_grid_site_expansion
-- name    : OAI.Erdos3.VectorPolynomial.exists_allocatedSupportedSliced_full_grid_site_expansion
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-10T06:21:19.895035+00:00
-- url     : https://prove2.me/theorems/09c4c903-2369-4086-95ba-34b8c9b63632
-- title:
--   A family of site expansions approximates the full grid density of the sliced law
-- statement:
--   Fix the section data: a natural number $m$; a finite type $G$; finite types $I_j$ with decidable equality and natural numbers $n_j$ ($j \in \mathrm{Fin}\,m$); finite types $B_a$ with decidable equality over the axes $a$ of `LayerSamplerAxis I n` (the sigma type $\Sigma_j\, I_j \oplus \mathrm{Fin}(n_j)$); finite types $J_j$, real subspaces $U_j \subseteq \mathbb R^{J_j}$ and bases $b_j$ (indexed by $\mathrm{Fin}\,n_j$) of the orthogonal complements of `euclideanSubspace (U j)`; real functions $R, \sigma$ on $\mathrm{Fin}\,m$ with $R_j > 0$ (hR) and $\sigma_j > 0$ (hσ); a `LayerSamplerScale` $S$ (a structure bundling a positive natural number $S.\mathrm{value}$ with width and gap inequalities); a finite type $\alpha$ with decidable equality and finite families $\mathrm{rowSets}_j$ of finsets of $\alpha$ (rowTypes$_j$ is the subtype of $\mathrm{rowSets}_j$); FullInput $=$ `PrincipalTupleIndex B (layerSamplerDegree I n)`; $H, \mathrm{step} : \mathrm{FullInput} \to \mathbb N$ and $c : \mathrm{FullInput} \to \mathbb Z$ with $H_t > 0$ (hH) and each progression `integerProgressionSupport (c t) (step t) (H t)` $= \{c_t + \mathrm{step}_t k : 0 \le k < H_t\}$ contained in $[0,$ `allocatedPrincipalSides B U b S t`$)$ (hsubset); and $q \in \mathbb N$, $r : \mathrm{FullInput} \to \mathrm{Option}\,\alpha \to \mathbb Z/q$ with the residue cell $\{y : \texttt{principalResidueLabel q y} = r\}$ of positive mass under `principalTupleWeights B (layerSamplerDegree I n) H hH` (hcell). Let gridAxes be the axes satisfying `allocatedGridAxis U b S.value`.
--
--   Assume $q > 0$; let $\delta > 0$ with $\delta\cdot$`allocatedPrincipalSides B U b S t` $\le H_t$ for all $t$; let $T \in \mathbb N$ with $(|\alpha|+1)q/\delta \le T$; assume $\mathrm{step}_t > 0$ for all $t$; let $A \in \mathbb R_{\ge 0}$ with `Real.smoothTransition` $A$-Lipschitz; let $P \ge 1$ with `scalarCubePrimitiveEnvelope Empty A 16 (128 * probabilityProfileLipschitz) 1` $\le P$, `scalarCubePrimitiveEnvelope α A 1 0 q` $\le P$ and $\mathrm{step}_t\, q \le P$ for all $t$; assume every $t \in \mathrm{rowSets}_j$ has $|t| \le j+1$, and for all $j$ and $i \in \mathrm{Fin}(n_j)$, `positiveModerateSpectrumBlockCount j |rowSets j| ((layerTailDegree m + 1)|rowSets j|)` $\le |B_{\langle j,\mathrm{inr}\,i\rangle}|$ and `uniformSpectrumBlockCount j |rowSets j| ((j+1)|rowSets j|)` $\le |B_{\langle j,\mathrm{inr}\,i\rangle}|$. Let $D, v, w, t, p_0, E, \varepsilon$ be reals with $D, v, w, t, p_0, E \ge 0$; $|\alpha| \le D$; $j+1 \le D$, $|\mathrm{rowSets}_j| \le D$, $R_j \le e^v$, $R_j^{-1} \le e^v$, $|\texttt{BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j+1)}| \le e^v$ and $\sigma_j \le 1$ for all $j$; `layerTailDegree m` $+1 \le D$; $|B_{\langle j,\mathrm{inr}\,i\rangle}| \le D$ for all $j, i$; $\delta^{-1} \le e^w$; $T \le e^t$; $P \le e^{p_0}$; $|\mathrm{gridAxes}| \le D$; and $\varepsilon > 0$ with $\varepsilon^{-1} \le e^E$. Put $p =$ `slicedGridGeometryLog D v w t` $+ p_0$, $L_j(e) =$ `slicedGridSiteLog j |rowSets j| ((layerTailDegree m + 1)|rowSets j|) ((j+1)|rowSets j|) D p e`, $C_p = \sum_j (L_j(0) + D(v+1))$, $E' =$ `uniformProductAccuracyLog D Cp E` $+ D(v+1) + 1$, and $O_p = \sum_j\bigl(\texttt{siteExponentialOutputLog}(2^{|\alpha|}, L_j(E')) + (D+1)(v+1)\bigr)$.
--
--   Then there exists a family $e$ of `ScalarSiteExpansion`s on $\mathrm{Finset}\,\alpha$, one for each grid axis (each a finite family of terms $k$ with a period $p_k$, a coefficient $a_k \in \mathbb C$ and factors $\phi_{k,s} : \mathbb Z/p_k \times \mathbb R \to \mathbb C$), such that:
--
--   - for every grid axis $a$, `(e a).Bounds` $(e^{O_p}, e^{O_p}, e^{O_p}, e^{O_p}, \exp(\texttt{slicedGridGeometryLog D v w t} + D + v + 8))$ holds: at most $e^{O_p}$ terms, periods in $(0, e^{O_p}]$, $\sum_k |a_k| \le e^{O_p}$, every factor of norm at most $1$ and $e^{O_p}$-Lipschitz in its real argument, and vanishing at real arguments $x$ with $|x| \ge \exp(\texttt{slicedGridGeometryLog D v w t} + D + v + 8)$; and
--   - for every $x : G \to$ `IntegerScalarCubeBox α S.value` and every $z$ in `AllocatedFrozenJetRows B U b S rowTypes` (a jet row for each grid axis),
--   $$\bigl\| \texttt{allocatedFullGridNaturalVolume B U b S rowSets}\cdot\texttt{allocatedSupportedSlicedFullGridDensity B U b hR hσ S rowSets H step c hH hsubset q r hcell x z} - \texttt{allocatedFullGridSiteApproximation B U b S rowSets e z} \bigr\| \le \varepsilon,$$
--   where the volume is $\prod_{a \in \mathrm{gridAxes}} N_a^{|\mathrm{rowSets}_{\mathrm{layer}(a)}|}$ with $N_a$ = `allocatedGridNaturalScale B U b S a`, the density is the product over grid axes of the supported sliced grid PMFs, and the approximation evaluates the family $e$ (`siteFamilyEval`) at the integer site values of $z$ and their quotients by $N_a$.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.exists_allocatedSupportedSliced_full_grid_site_expansion` in `lean/OAI/Combinatorics/Progressions/Sampling/AllocatedSupportedSlicedFullGridSite.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B177` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Sampling/AllocatedSupportedSlicedFullGridSite.lean#L720

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B177

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

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

universe uα

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

local notation "gridAxes" => {a // allocatedGridAxis (I := I) U b S.value a}
local notation "ig" => allocatedGridIntegerAxis B U b S
local notation "axisN" => allocatedGridNaturalScale B U b S
local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset α))

variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ j, 0 < H j)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U b S j : ℤ))
variable (q : ℕ) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n) H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "gridLaw" => containedSupportedProgressionAxisLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) H step c (allocatedPrincipalSides_pos B U b S) hH hsubset q r hcell grid
local notation "height" => (fun a : gridAxes => basisAxisScale (b (Sigma.fst (ig a))) (Sigma.snd (ig a)))

theorem exists_allocatedSupportedSliced_full_grid_site_expansion
    (hq : 0 < q) {δ : ℝ} (hδ : 0 < δ)
    (hdense : ∀ t, δ * allocatedPrincipalSides B U b S t ≤ (H t : ℝ))
    (T : ℕ) (hQT : (((Fintype.card α + 1) * q : ℕ) : ℝ) / δ ≤ T)
    (hstep : ∀ t, 0 < step t)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) (P : ℝ) (hP : 1 ≤ P)
    (hcP : scalarCubePrimitiveEnvelope Empty A 16 (128 * probabilityProfileLipschitz) 1 ≤ P)
    (hsP : scalarCubePrimitiveEnvelope α A 1 0 q ≤ P)
    (hstride : ∀ t, ((step t * q : ℕ) : ℝ) ≤ P)
    (hrows : ∀ j t, t ∈ rowSets j → t.card ≤ j.val + 1)
    (hBa : ∀ j i, positiveModerateSpectrumBlockCount j.val (rowSets j).card
      ((layerTailDegree m + 1) * (rowSets j).card) ≤ Fintype.card (B ⟨j,Sum.inr i⟩))
    (hBi : ∀ j i, uniformSpectrumBlockCount j.val (rowSets j).card
      ((j.val + 1) * (rowSets j).card) ≤ Fintype.card (B ⟨j,Sum.inr i⟩))
    {D v w t p₀ E ε : ℝ}
    (hD : 0 ≤ D) (hv : 0 ≤ v) (hw : 0 ≤ w) (ht : 0 ≤ t) (hp₀ : 0 ≤ p₀) (hE : 0 ≤ E)
    (hcube : (Fintype.card α : ℝ) ≤ D) (hdegree : ∀ j : Fin m, ((j.val + 1 : ℕ) : ℝ) ≤ D)
    (hrowsD : ∀ j, ((rowSets j).card : ℝ) ≤ D)
    (htail : ((layerTailDegree m + 1 : ℕ) : ℝ) ≤ D)
    (hblocks : ∀ j i, (Fintype.card (B ⟨j, Sum.inr i⟩) : ℝ) ≤ D)
    (hRv : ∀ j, R j ≤ Real.exp v) (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp v)
    (hδw : δ⁻¹ ≤ Real.exp w) (hT : (T : ℝ) ≤ Real.exp t)
    (hcoeff : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ Real.exp v)
    (hPp₀ : P ≤ Real.exp p₀) (haxes : (Fintype.card gridAxes : ℝ) ≤ D)
    (hε : 0 < ε) (hεE : ε⁻¹ ≤ Real.exp E) (hσ1 : ∀ j, σ j ≤ 1) :
    let p := slicedGridGeometryLog D v w t + p₀
    let L := fun j : Fin m => fun e : ℝ => slicedGridSiteLog j.val (rowSets j).card
      ((layerTailDegree m + 1) * (rowSets j).card) ((j.val + 1) * (rowSets j).card) D p e
    let Cp := ∑ j, (L j 0 + D * (v + 1))
    let E' := uniformProductAccuracyLog D Cp E + D * (v + 1) + 1
    let Op := ∑ j, (siteExponentialOutputLog (Fintype.card (Finset α)) (L j E') + (D + 1) * (v + 1))
    ∃ e : gridAxes → ScalarSiteExpansion.{uα,uα} (Finset α),
      (∀ a, (e a).Bounds (Real.exp Op) (Real.exp Op) (Real.exp Op)
        ⟨Real.exp Op, Real.exp_nonneg _⟩ (Real.exp (slicedGridGeometryLog D v w t + (D + v + 8)))) ∧
      ∀ (x : G → IntegerScalarCubeBox α S.value) (z : AllocatedFrozenJetRows B U b S rowTypes),
        ‖(allocatedFullGridNaturalVolume B U b S rowSets : ℂ) *
          (allocatedSupportedSlicedFullGridDensity B U b hR hσ S rowSets H step c hH hsubset q r hcell x z : ℂ) -
          allocatedFullGridSiteApproximation B U b S rowSets e z‖ ≤ ε := by
  sorry

end Erdos3.VectorPolynomial
end
end OAI
