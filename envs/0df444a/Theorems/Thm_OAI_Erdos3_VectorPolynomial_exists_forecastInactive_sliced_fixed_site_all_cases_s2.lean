-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_exists_forecastInactive_sliced_fixed_site_all_cases_s2
-- name    : OAI.Erdos3.VectorPolynomial.exists_forecastInactive_sliced_fixed_site_all_cases_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T04:30:07.723745+00:00
-- url     : https://prove2.me/theorems/232008ae-24ce-41c4-b602-7870b7f50008
-- title:
--   On a short grid axis, the scaled supported sliced residue jet PMF is approximated by a bounded scalar site expansion
-- statement:
--   All named objects below are defined by OpenAI.
--
--   **Setting.** Let $m$ be a natural number, $G$ a finite type, $I_j$ ($j<m$) finite types with decidable equality, $n : \mathrm{Fin}(m)\to\mathbb{N}$, $B_a$ finite types with decidable equality indexed by `LayerSamplerAxis I n` $= \Sigma_j (I_j \sqcup \mathrm{Fin}(n_j))$, $J_j$ finite types, $U_j \subseteq \mathbb{R}^{J_j}$ subspaces, `basis j` bases (indexed by $\mathrm{Fin}(n_j)$) of the orthogonal complement of `euclideanSubspace (U j)`, $R, \sigma$ with $R_j > 0$ and $\sigma_j > 0$, and `S : LayerSamplerScale B U basis R σ`. Let $\alpha$ be a finite type with decidable equality. Write $\mathcal{P}$ = `PrincipalTupleIndex B (layerSamplerDegree I n)` and `sides` = `allocatedPrincipalSides B U basis S`. Let $q > 0$ be a natural number and $r : \mathcal{P} \to \mathrm{Option}\ \alpha \to \mathbb{Z}/q\mathbb{Z}$; let $H, \mathrm{step} : \mathcal{P} \to \mathbb{N}$ and $\mathrm{lower} : \mathcal{P} \to \mathbb{Z}$ with $H_t > 0$, each progression $\{\mathrm{lower}_t + \mathrm{step}_t\,k : k < H_t\}$ contained in $[0, \texttt{sides}_t)$, and positive mass of the residue-$r$ cell under `principalTupleWeights B (layerSamplerDegree I n) H hH` (`hcell`). Fix a layer $j < m$ and an integer axis $i \in \mathrm{Fin}(n_j)$, and let $\delta, P, \varepsilon$ be reals and `rows` a finite set of finite subsets of $\alpha$.
--
--   **Abbreviations.** $h$ = `basisAxisScale (basis j) i` (a natural number, the height); $k = j + 1$ (the degree); $\mathrm{denom}$ = `inactiveDenominator (principalProfileSize (R j) |layerIntegerPrincipalSlots B j i|)` and $\mathrm{cost} = \mathrm{denom}\cdot 2^{k}$; $\mathrm{torus}$ = `blockTorusFactor |α| k |B (j, inr i)| 1`; `constantLaw` = `allocatedLayerIntegerPMFs B U basis hR hσ S j i (principalCoefficientChoice (layerSamplerDegree I n) (j, inr i) none)`; $\mathrm{Slots}$ = `BoundedCoefficientExponent (LayerSamplerVariables G I n B) k`; $\mathrm{radius} = |\mathrm{Slots}|\cdot(2^{|\alpha|}(|\alpha|+1)^{k})\cdot R_j$; $V = \mathrm{torus}\cdot\mathrm{cost}/\delta^{k}$; $t = k\,|\mathrm{rows}|$; $W = (\mathrm{torus}\cdot\mathrm{cost})^{|\mathrm{rows}|}/\delta^{t}$; $\mathrm{bias}$ = `uniformBlockRetainedBias j |rows| t P V W ε`; $\mathrm{freq}$ = `Real.toNNReal (uniformScaledRetainedFrequencyBound j |rows| P V bias)`; $\mathrm{cap}$ = `uniformSpectrumAbsoluteCap j |rows| t P V W`; $\mathrm{sizeBound}$ = `uniformSpectrumSizeConstant j |rows| t P V W` $/\ \varepsilon^{\max(\texttt{majorArcSpectrumExponent}\ j\ |\mathrm{rows}|,\ \texttt{majorArcLengthExponent}\ j\cdot t)}$; $\mathrm{periodBound}$ = `uniformScaledRetainedDenominatorBound j |rows| t P V W bias`; $\mathrm{cutoff}$ = `allocatedSlicedGridHeightCutoff B j i ⌈(|α|+1) q / δ⌉₊` (with $R$).
--
--   **Hypotheses.** $\delta > 0$; for all $b, v$: $\delta\cdot\texttt{sides}_{(j,\mathrm{inr}\ i),b,v} \le H_{(j,\mathrm{inr}\ i),b,v}$ and $\mathrm{step}_{(j,\mathrm{inr}\ i),b,v} > 0$; $h \le \texttt{S.value}^{k}$; the axis $(j, \mathrm{inr}\ i)$ is a grid axis (`allocatedGridAxis U basis S.value`); $c_0 \in \mathbb{Z}$ with `constantLaw c0` $\ne 0$; $\sigma_j \le 1$; $A \in \mathbb{R}_{\ge 0}$ a Lipschitz constant of `Real.smoothTransition`; $1 \le P$ and `scalarCubePrimitiveEnvelope α A 1 0 q` $\le P$; $\mathrm{step}_{(j,\mathrm{inr}\ i),b,v}\cdot q \le P$ for all $b, v$; $0 < \varepsilon \le 1$; every $u \in \mathrm{rows}$ has $|u| \le k$; `uniformSpectrumBlockCount j |rows| t` $\le |B_{(j,\mathrm{inr}\ i)}|$; reals $\eta > 0$ and $Q \ge 0$ with
--   $|\mathrm{rows}|\cdot\mathrm{radius} + 1/4 \le e^{Q}$, $(\eta/(\mathrm{cap}+1))^{-1} \le e^{Q}$, $(\texttt{characterLipConstant}\cdot(|\mathrm{rows}|\cdot\mathrm{freq}) + 4)\cdot 2^{|\alpha|} \le e^{Q}$, $\mathrm{cutoff}^{|\mathrm{rows}|} \le e^{Q}$, $(|\mathrm{rows}|\cdot 2\,\mathrm{cutoff}^2\cdot\mathrm{cutoff}^{|\mathrm{rows}|})\cdot 2^{|\alpha|} \le e^{Q}$, and $\eta^{-1} \le e^{Q}$.
--
--   **Conclusion.** Write $F = 2^{|\alpha|} = |\mathrm{Finset}\ \alpha|$ and $\Theta = F(4Q + 8)$. There is a scalar site expansion $e$ over $\mathrm{Finset}\ \alpha$ (`ScalarSiteExpansion`: a finite set of terms $i$, each with a positive period $p_i$, a coefficient $a_i \in \mathbb{C}$ and factors $\phi_{i,s}(\rho, x) \in \mathbb{C}$ for $s \in \mathrm{Finset}\ \alpha$, $\rho \in \mathbb{Z}/p_i$, $x \in \mathbb{R}$) satisfying `e.Bounds` with: number of terms at most $\max(\mathrm{sizeBound}\cdot e^{\Theta}, e^{\Theta})$; every period positive and at most $\max(\mathrm{periodBound}, 1)$; $\sum_i |a_i| \le \max(\mathrm{cap}\cdot e^{\Theta + Q}, e^{\Theta + Q})$; every factor of norm at most $1$; every $\phi_{i,s}(\rho, \cdot)$ Lipschitz with constant $e^{1 + 6Q + 12} + 4$; and $\phi_{i,s}(\rho, x) = 0$ whenever $|x| \ge |\mathrm{rows}|\cdot\mathrm{radius} + 1/4$. Moreover, for every $y : \mathrm{Finset}\ \alpha \to \mathbb{Z}$ whose Boolean (Möbius) coefficients `booleanCoefficient y u` $= \sum_{t \subseteq u} (-1)^{|u \setminus t|} y(t)$ vanish for all $u \notin \mathrm{rows}$,
--   $$\Bigl\| h^{|\mathrm{rows}|}\cdot \pi\bigl(u \mapsto \texttt{booleanCoefficient}(\mathrm{const}\ c_0)\ u,\ u \mapsto \texttt{booleanCoefficient}\ y\ u\bigr) - \texttt{e.integerEval}\ h\ y \Bigr\| \le \varepsilon + \eta,$$
--   where $\pi$ is the real value of `allocatedSupportedSlicedResidueJetPMF B U basis hR hσ S q r H step lower hH hsubset hcell j i rows`, and `e.integerEval h y` $= \sum_i a_i \prod_s \phi_{i,s}(y(s) \bmod p_i,\ y(s)/h)$.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.exists_forecastInactive_sliced_fixed_site_all_cases_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.exists_forecastInactive_sliced_fixed_site_all_cases` (in `lean/OAI/Combinatorics/Progressions/Sampling/ForecastInactiveSlicedFixedAxisCap.lean`); the definitions it uses are in the definitions bundles `OAIE3v2B180`, `OAIE3v2B196` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Sampling/ForecastInactiveSlicedFixedAxisCap.lean (declaration OAI.Erdos3.VectorPolynomial.exists_forecastInactive_sliced_fixed_site_all_cases)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B180
import Definitions.Def_OAIE3v2B196

section

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

universe uα

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (q : ℕ) (hq : 0 < q) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (lower : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ t, 0 < H t)
variable (hsubset : ∀ t, integerProgressionSupport (lower t) (step t : ℤ) (H t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ))
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n) H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
variable (j : Fin m) (i : Fin (n j))

local notation "height" => basisAxisScale (basis j) i
local notation "degree" => j.val + 1
local notation "denom" => inactiveDenominator
  (principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i)))
local notation "cost" => (denom : ℝ) * 2 ^ degree
local notation "torus" => blockTorusFactor (Fintype.card α) degree
  (Fintype.card (B (Sigma.mk j (Sum.inr i)))) 1
local notation "constantLaw" => allocatedLayerIntegerPMFs B U basis hR hσ S j i
  (principalCoefficientChoice (G := G) (layerSamplerDegree I n) (Sigma.mk j (Sum.inr i)) none)
local notation "Slots" => BoundedCoefficientExponent (LayerSamplerVariables G I n B) degree
local notation "radius" => (Fintype.card Slots : ℝ) *
  ((2 : ℝ) ^ Fintype.card α * ((Fintype.card α : ℝ) + 1) ^ degree) * R j

variable (δ P ε : ℝ) (rows : Finset (Finset α))

local notation "V" => (torus : ℝ) * cost / δ ^ degree
local notation "t" => degree * rows.card
local notation "W" => ((torus : ℝ) * cost) ^ rows.card / δ ^ t
local notation "bias" => uniformBlockRetainedBias j.val rows.card t P V W ε
local notation "freq" => Real.toNNReal (uniformScaledRetainedFrequencyBound j.val rows.card P V bias)
local notation "cap" => uniformSpectrumAbsoluteCap j.val rows.card t P V W
local notation "sizeBound" => uniformSpectrumSizeConstant j.val rows.card t P V W /
  ε ^ max (majorArcSpectrumExponent j.val rows.card) (majorArcLengthExponent j.val * t)
local notation "periodBound" => uniformScaledRetainedDenominatorBound j.val rows.card t P V W bias
local notation "cutoff" => allocatedSlicedGridHeightCutoff (G := G) B (R := R) j i
  (Nat.ceil (((((Fintype.card α + 1) * q) : ℕ) : ℝ) / δ))

include hq in
theorem exists_forecastInactive_sliced_fixed_site_all_cases_s2
    (hδ : 0 < δ)
    (hdense : ∀ b v, δ * allocatedPrincipalSides B U basis S ⟨⟨j,Sum.inr i⟩,b,v⟩ ≤
      (H ⟨⟨j,Sum.inr i⟩,b,v⟩ : ℝ))
    (hstep : ∀ b v, 0 < step ⟨⟨j,Sum.inr i⟩,b,v⟩)
    (hsmall : height ≤ S.value ^ degree)
    (hgrid : allocatedGridAxis (I := I) U basis S.value ⟨j, Sum.inr i⟩)
    (c0 : ℤ) (hc0 : constantLaw c0 ≠ 0)
    (hσ1 : σ j ≤ 1) (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition)
    (hP : 1 ≤ P) (hsP : scalarCubePrimitiveEnvelope α A 1 0 q ≤ P)
    (hstride : ∀ b v, ((step ⟨⟨j,Sum.inr i⟩,b,v⟩ * q : ℕ) : ℝ) ≤ P)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hrows : ∀ u ∈ rows, u.card ≤ degree)
    (hB : uniformSpectrumBlockCount j.val rows.card t ≤ Fintype.card (B ⟨j, Sum.inr i⟩))
    {η Q : ℝ} (hη : 0 < η) (hQ : 0 ≤ Q)
    (hRQ : rows.card * radius + 1 / 4 ≤ Real.exp Q)
    (hηQ : (η / (cap + 1))⁻¹ ≤ Real.exp Q)
    (hLQ : ((CircleFourier.characterLipConstant * (rows.card * freq) + 4) *
      (2 : ℝ≥0) ^ Fintype.card α : ℝ≥0) ≤ Real.exp Q)
    (hshortCap : (cutoff : ℝ) ^ rows.card ≤ Real.exp Q)
    (hshortLip : ((rows.card * (2 * (cutoff : ℝ≥0) ^ 2) * (cutoff : ℝ≥0) ^ rows.card) *
      (2 : ℝ≥0) ^ Fintype.card α : ℝ≥0) ≤ Real.exp Q)
    (hshortError : η⁻¹ ≤ Real.exp Q) :
    ∃ e : ScalarSiteExpansion.{uα,uα} (Finset α),
      e.Bounds
        (max (sizeBound * Real.exp (Fintype.card (Finset α) * (4 * Q + 8)))
          (Real.exp (Fintype.card (Finset α) * (4 * Q + 8))))
        (max periodBound 1)
        (max (cap * Real.exp (Fintype.card (Finset α) * (4 * Q + 8) + Q))
          (Real.exp (Fintype.card (Finset α) * (4 * Q + 8) + Q)))
        (⟨Real.exp (1 + 6 * Q + 12), Real.exp_nonneg _⟩ + 4) (rows.card * radius + 1 / 4) ∧
      ∀ y : Finset α → ℤ, (∀ u ∉ rows, booleanCoefficient y u = 0) →
        ‖(((height : ℝ) ^ rows.card *
          (allocatedSupportedSlicedResidueJetPMF B U basis hR hσ S q r H step lower hH hsubset hcell j i rows
            (fun u => booleanCoefficient (fun _ : Finset α => c0) u)
            (fun u => booleanCoefficient y u)).toReal : ℝ) : ℂ) - e.integerEval height y‖ ≤ ε + η := by
  sorry

end Erdos3.VectorPolynomial

end

end OAI
end
