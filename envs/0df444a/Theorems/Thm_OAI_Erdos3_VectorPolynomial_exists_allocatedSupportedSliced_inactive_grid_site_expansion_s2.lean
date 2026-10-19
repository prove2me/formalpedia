-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_exists_allocatedSupportedSliced_inactive_grid_site_expansion_s2
-- name    : OAI.Erdos3.VectorPolynomial.exists_allocatedSupportedSliced_inactive_grid_site_expansion_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T04:28:41.257403+00:00
-- url     : https://prove2.me/theorems/c346b150-9215-444b-a08c-3e67cf37d765
-- title:
--   A bounded scalar site expansion approximates the supported sliced physical grid mass on an inactive grid axis
-- statement:
--   **Setting.** Let $m$ be a natural number, $G$ a finite type, $I : \mathrm{Fin}\ m \to \mathrm{Type}$ a family of finite types with decidable equality, $n : \mathrm{Fin}\ m \to \mathbb{N}$, $B$ a family of finite types with decidable equality indexed by `LayerSamplerAxis I n`, $J$ a family of finite types indexed by $\mathrm{Fin}\ m$, $U_j$ a real subspace of $J_j \to \mathbb{R}$, and $\mathrm{basis}_j$ a basis indexed by $\mathrm{Fin}\ (n\ j)$ of the orthogonal complement of `euclideanSubspace (U j)`. Let $R, \sigma : \mathrm{Fin}\ m \to \mathbb{R}$ with $R_j > 0$, $\sigma_j > 0$ for all $j$, and $S$ a `LayerSamplerScale B U basis R σ` (defined by OpenAI, with positive natural number $L$ = `S.value`). Let $\alpha$ be a finite type with decidable equality. Let $q > 0$ be a natural number and $r :$ `PrincipalTupleIndex B (layerSamplerDegree I n)` $\to \mathrm{Option}\ \alpha \to \mathbb{Z}/q$. Let $H, \mathrm{step} :$ `PrincipalTupleIndex B (layerSamplerDegree I n)` $\to \mathbb{N}$ and $c$ to $\mathbb{Z}$, with $H_t > 0$ for all $t$, and with `integerProgressionSupport (c t) (step t) (H t)` $= \{c_t + \mathrm{step}_t v : 0 \le v < H_t\}$ contained in $[0,$ `allocatedPrincipalSides B U basis S t`$)$ for all $t$ (hypothesis $hsubset$). Suppose the residue cell $\{y : \texttt{principalResidueLabel}\ q\ y = r\}$ has positive mass under `principalTupleWeights B (layerSamplerDegree I n) H hH` (hypothesis $hcell$). Let $j \in \mathrm{Fin}\ m$ and $i \in \mathrm{Fin}\ (n\ j)$, write $a = \langle j, \mathrm{inr}\ i\rangle$ for the corresponding axis, and suppose $(|\alpha| + 1)\,q \le H_{\langle a, b, v\rangle}$ for all $b \in B\ a$ and $v \in \mathrm{Fin}\ (j + 1)$.
--
--   Write $h$ = `basisAxisScale (basis j) i` $= \lceil \lVert \mathrm{basis}_j(i) \rVert^{-1} \rceil$ (natural-number ceiling), $k = j + 1$, $\mathrm{den}$ = `inactiveDenominator (principalProfileSize (R j) |layerIntegerPrincipalSlots B j i|)` (with `principalProfileSize R b` $= R/(8(b+1))$ and `inactiveDenominator γ` $= \max(1, \lceil \gamma^{-1} \rceil)$), $\mathrm{side}$ = `inactiveSideLength k h den` (the integer $k$-th root of $\lfloor h/\mathrm{den} \rfloor$ when $2\,\mathrm{den} \le h$, else $1$), $\mathrm{cost} = \mathrm{den}\cdot 2^{k}$, and $\mathrm{torus}$ = `blockTorusFactor |α| k |B a| 1` (a positive integer defined by OpenAI).
--
--   **Hypotheses.** Suppose the axis $a$ satisfies `allocatedGridAxis U basis S.value`; $h \le L^{k}$; $2\,\mathrm{den} \le h$; $\delta > 0$ is real with $\delta\cdot\mathrm{side} \le H_{\langle a, b, v\rangle}$ and $0 < \mathrm{step}_{\langle a, b, v\rangle}$ for all $b, v$; $A \in \mathbb{R}_{\ge 0}$ is such that `Real.smoothTransition` is $A$-Lipschitz; $P \ge 1$ is real with `scalarCubePrimitiveEnvelope α A 1 0 q` $\le P$ and $\mathrm{step}_{\langle a, b, v\rangle}\cdot q \le P$ for all $b, v$; $\varepsilon$ is real, $M$ is a nonzero natural number with $M = \mathrm{torus}\cdot h$; $\mathrm{rows}$ is a finite set of finite subsets of $\alpha$, each of size at most $k$, with `uniformSpectrumBlockCount j |rows| (k |rows|)` $\le |B\ a|$; $0 < \varepsilon \le 1$; and $\sigma_j \le 1$.
--
--   **Conclusion.** Put $V = \mathrm{torus}\cdot\mathrm{cost}/\delta^{k}$, $t = k\,|\mathrm{rows}|$, $W = (\mathrm{torus}\cdot\mathrm{cost})^{|\mathrm{rows}|}/\delta^{t}$, $\zeta$ = `uniformBlockRetainedBias j |rows| t P V W ε`, $\mathrm{freq}$ = `uniformScaledRetainedFrequencyBound j |rows| P V ζ` (truncated at $0$), $\mathrm{cap}$ = `uniformSpectrumAbsoluteCap j |rows| t P V W` (explicit functions defined by OpenAI), and
--   $$R_0 = |\mathrm{rows}|\cdot\Bigl(|\texttt{BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j + 1)}|\cdot\bigl(2^{|\alpha|}(|\alpha| + 1)^{j+1}\bigr)\cdot R_j\Bigr).$$
--   Then for all real $\eta, Q$ with $\eta > 0$, $Q \ge 0$, $R_0 + 1/4 \le e^{Q}$, $(\eta/(\mathrm{cap} + 1))^{-1} \le e^{Q}$, and $(\texttt{CircleFourier.characterLipConstant}\cdot(|\mathrm{rows}|\,\mathrm{freq}) + 4)\cdot 2^{|\alpha|} \le e^{Q}$, there is a `ScalarSiteExpansion (Finset α)` $e$ (a structure defined by OpenAI: a finite family of terms, each with a positive period, a complex coefficient, and a factor function for each site) such that:
--
--   - `e.Bounds T D C L' H'` holds (the number of terms is at most $T$, each period lies in $(0, D]$, the coefficients have absolute sum at most $C$, every factor has norm at most $1$, is $L'$-Lipschitz in the real variable and vanishes when that variable has absolute value at least $H'$), with
--     $T = \bigl(\texttt{uniformSpectrumSizeConstant j |rows| t P V W} / \varepsilon^{\max(\texttt{majorArcSpectrumExponent j |rows|},\ \texttt{majorArcLengthExponent j}\cdot t)}\bigr)\cdot \exp\bigl(|\mathrm{Finset}\ \alpha|\,(4Q + 8)\bigr)$,
--     $D$ = `uniformScaledRetainedDenominatorBound j |rows| t P V W ζ`,
--     $C = \mathrm{cap}\cdot \exp\bigl(|\mathrm{Finset}\ \alpha|\,(4Q + 8) + Q\bigr)$,
--     $L' = e^{1 + 6Q + 12} + 4$, and $H' = R_0 + 1/4$;
--   - for every $x : G \to$ `IntegerScalarCubeBox α S.value` and every $y : \mathrm{Finset}\ \alpha \to \mathbb{Z}$ such that `booleanCoefficient y t` $= \sum_{t' \subseteq t} (-1)^{|t \setminus t'|} y(t')$ vanishes for every $t \notin \mathrm{rows}$,
--   $$\Bigl\lVert h^{|\mathrm{rows}|}\cdot \mu_x\bigl(t \mapsto \texttt{booleanCoefficient}\ y\ t\bigr) - \texttt{e.integerEval}\ h\ y \Bigr\rVert \le \varepsilon + \eta,$$
--   where $\mu_x$ = `allocatedSupportedSlicedPhysicalGridPMF B U basis hR hσ S q r H step c hH hsubset hcell j i rows x` is a probability mass function on $\mathrm{rows} \to \mathbb{Z}$ defined by OpenAI (its value at the given point is taken as a real number), and `e.integerEval h y` $= \sum_{\mathrm{terms}\ \ell} \mathrm{coefficient}_\ell \prod_{s} \mathrm{factor}_\ell(s, y(s) \bmod \mathrm{period}_\ell, y(s)/h)$.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.exists_allocatedSupportedSliced_inactive_grid_site_expansion_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.exists_allocatedSupportedSliced_inactive_grid_site_expansion` (in `lean/OAI/Combinatorics/Progressions/Sampling/AllocatedSupportedSlicedInactiveGridSite.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B196` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Sampling/AllocatedSupportedSlicedInactiveGridSite.lean (declaration OAI.Erdos3.VectorPolynomial.exists_allocatedSupportedSliced_inactive_grid_site_expansion)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B196

section

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

variable (hsize : ∀ b v, (Fintype.card α + 1) * q ≤ H ⟨⟨j,Sum.inr i⟩,b,v⟩)

local notation "height" => basisAxisScale (basis j) i
local notation "degree" => Fin.val j + 1
local notation "denom" => inactiveDenominator
  (principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i)))
local notation "side" => inactiveSideLength degree height denom
local notation "cost" => (denom : ℝ) * 2 ^ degree
local notation "sources" => principalSupportedAxisSources B (layerSamplerDegree I n) H hH q hq r
  (Sigma.mk j (Sum.inr i)) hsize
local notation "lower" => (fun (b : B (Sigma.mk j (Sum.inr i))) (v : Fin degree) (a : Option α) =>
  ite (a = none) (c (Sigma.mk (Sigma.mk j (Sum.inr i)) (Prod.mk b v))) 0)
local notation "strides" => (fun (b : B (Sigma.mk j (Sum.inr i))) (v : Fin degree) (_ : Option α) =>
  step (Sigma.mk (Sigma.mk j (Sum.inr i)) (Prod.mk b v)))

local notation "radius" => blockJetScaleBound (Fintype.card α) degree (Fintype.card (B (Sigma.mk j (Sum.inr i)))) 1
local notation "torus" => blockTorusFactor (Fintype.card α) degree (Fintype.card (B (Sigma.mk j (Sum.inr i)))) 1

local notation "constantLaw" => allocatedLayerIntegerPMFs B U basis hR hσ S j i
  (principalCoefficientChoice (G := G) (layerSamplerDegree I n) (Sigma.mk j (Sum.inr i)) none)

include hq hsize in
theorem exists_allocatedSupportedSliced_inactive_grid_site_expansion_s2
    (hgrid : allocatedGridAxis (I := I) U basis S.value ⟨j, Sum.inr i⟩)
    (hsmall : height ≤ S.value ^ degree) (hlarge : 2 * denom ≤ height)
    {δ : ℝ} (hδ : 0 < δ)
    (hlength : ∀ b v, δ * side ≤ (H ⟨⟨j,Sum.inr i⟩,b,v⟩ : ℝ))
    (hstep : ∀ b v, 0 < step ⟨⟨j,Sum.inr i⟩,b,v⟩)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) (P : ℝ) (hP : 1 ≤ P)
    (hsP : scalarCubePrimitiveEnvelope α A 1 0 q ≤ P)
    (hstride : ∀ b v, ((step ⟨⟨j,Sum.inr i⟩,b,v⟩ * q : ℕ) : ℝ) ≤ P)
    {ε : ℝ} {M : ℕ} [NeZero M] (hM : M = torus * height)
    (rows : Finset (Finset α)) (hrows : ∀ t ∈ rows, t.card ≤ degree)
    (hB : uniformSpectrumBlockCount j.val rows.card (degree * rows.card) ≤ Fintype.card (B ⟨j, Sum.inr i⟩))
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hσ1 : σ j ≤ 1) :
    let V := (torus : ℝ) * cost / δ ^ degree
    let t := degree * rows.card
    let W := ((torus : ℝ) * cost) ^ rows.card / δ ^ t
    let ζ := uniformBlockRetainedBias j.val rows.card t P V W ε
    let freq := Real.toNNReal (uniformScaledRetainedFrequencyBound j.val rows.card P V ζ)
    let cap := uniformSpectrumAbsoluteCap j.val rows.card t P V W
    let R0 := (rows.card : ℝ) *
      ((Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
        ((2 : ℝ) ^ Fintype.card α * ((Fintype.card α : ℝ) + 1) ^ (j.val + 1)) * R j)
    ∀ {η Q : ℝ}, 0 < η → 0 ≤ Q → R0 + 1 / 4 ≤ Real.exp Q →
      (η / (cap + 1))⁻¹ ≤ Real.exp Q →
      ((CircleFourier.characterLipConstant * (rows.card * freq) + 4) *
        (2 : ℝ≥0) ^ Fintype.card α : ℝ≥0) ≤ Real.exp Q →
    ∃ e : ScalarSiteExpansion.{uα,uα} (Finset α),
      e.Bounds
        ((uniformSpectrumSizeConstant j.val rows.card t P V W /
          ε ^ max (majorArcSpectrumExponent j.val rows.card) (majorArcLengthExponent j.val * t)) *
          Real.exp (Fintype.card (Finset α) * (4 * Q + 8)))
        (uniformScaledRetainedDenominatorBound j.val rows.card t P V W ζ)
        (cap * Real.exp (Fintype.card (Finset α) * (4 * Q + 8) + Q))
        (⟨Real.exp (1 + 6 * Q + 12), Real.exp_nonneg _⟩ + 4) (R0 + 1 / 4) ∧
      ∀ (x : G → IntegerScalarCubeBox α S.value) (y : Finset α → ℤ),
        (∀ t ∉ rows, booleanCoefficient y t = 0) →
        ‖(((height : ℝ) ^ rows.card *
          (allocatedSupportedSlicedPhysicalGridPMF B U basis hR hσ S q r H step c hH hsubset hcell j i rows x
            (fun t => booleanCoefficient y t)).toReal : ℝ) : ℂ) - e.integerEval height y‖ ≤ ε + η := by
  sorry

end Erdos3.VectorPolynomial

end

end OAI
end
