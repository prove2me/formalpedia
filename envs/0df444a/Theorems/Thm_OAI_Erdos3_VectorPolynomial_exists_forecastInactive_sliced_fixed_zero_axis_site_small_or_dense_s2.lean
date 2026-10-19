-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_exists_forecastInactive_sliced_fixed_zero_axis_site_small_or_dense_s2
-- name    : OAI.Erdos3.VectorPolynomial.exists_forecastInactive_sliced_fixed_zero_axis_site_small_or_dense_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T04:29:59.836925+00:00
-- url     : https://prove2.me/theorems/31692a16-a300-4b2b-b90d-f0486b5fd001
-- title:
--   On a small grid axis with zero-dimensional cube, the rescaled sliced residue jet law is uniformly approximated by a bounded scalar site expansion
-- statement:
--   **Setting.** Let $m \in \mathbb{N}$; let $G$ be a finite type; let $I_j$ ($j \in \mathrm{Fin}\,m$) be finite types with decidable equality, $n : \mathrm{Fin}\,m \to \mathbb{N}$, and $B_a$ finite types with decidable equality indexed by the sampler axes $a$ in `LayerSamplerAxis I n`; let $J_j$ be finite types, $U_j \subseteq \mathbb{R}^{J_j}$ subspaces, and $\mathrm{basis}_j$ a basis, indexed by $\mathrm{Fin}(n_j)$, of the orthogonal complement of $U_j$; let $R, \sigma : \mathrm{Fin}\,m \to \mathbb{R}$ with $R_j > 0$, $\sigma_j > 0$ for all $j$, and $S$ a `LayerSamplerScale B U basis R σ` (a structure defined by OpenAI, with positive natural-number value `S.value`). Write $\mathrm{Tuple}$ = `PrincipalTupleIndex B (layerSamplerDegree I n)` (triples (axis, block element, index)). Let $q$ be a positive natural number and $r : \mathrm{Tuple} \to \mathrm{Option}\,\emptyset \to \mathbb{Z}/q$; let $H, \mathrm{step} : \mathrm{Tuple} \to \mathbb{N}$ and $c : \mathrm{Tuple} \to \mathbb{Z}$ with $H_t > 0$ and the progression $\{c_t + \mathrm{step}_t k : 0 \le k < H_t\}$ contained in $[0, \texttt{allocatedPrincipalSides B U basis S}\ t)$ for every $t$; and assume (hypothesis $h_{\mathrm{cell}}$) that the residue cell $\{y : y \bmod q = r\}$ has positive mass under `principalTupleWeights` (with $\alpha = \emptyset$ and sides $H$). Fix $j \in \mathrm{Fin}\,m$, $i \in \mathrm{Fin}(n_j)$, and $H_{\mathrm{child}} \in \mathbb{N}$; write $\mathrm{deg} = j + 1$ and $a_0 = (j, \mathrm{inr}\, i)$ for the corresponding sampler axis.
--
--   Let $h$ = `basisAxisScale (basis j) i` $= \lceil \|\mathrm{basis}_j(i)\|^{-1} \rceil$ (a natural number); $\mathrm{denom}$ = `inactiveDenominator (principalProfileSize (R j) |layerIntegerPrincipalSlots B j i|)`; $\mathrm{cost} = \mathrm{denom} \cdot 2^{\mathrm{deg}}$; $\mathrm{torus}$ = `blockTorusFactor 0 deg |B_{a_0}| 1`; and let $\mu$ be the probability mass function on $\mathbb{Z}$ given by `allocatedLayerIntegerPMFs B U basis hR hσ S j i` at the constant-coefficient slot (`principalCoefficientChoice … a_0 none`). All of these are defined by OpenAI.
--
--   **Hypotheses.** Let $c_0 \in \mathbb{Z}$ with $\mu(c_0) \ne 0$. Assume $a_0$ is a grid axis (`allocatedGridAxis U basis S.value a_0`), $h \le S.\mathrm{value}^{\mathrm{deg}}$, and $\delta > 0$ with: either some side `allocatedPrincipalSides B U basis S (a_0, b_0, v_0)` is $< H_{\mathrm{child}}$, or for all $b, v$ both $\delta \cdot \texttt{allocatedPrincipalSides}(a_0, b, v) \le H_{(a_0, b, v)}$ and $\mathrm{step}_{(a_0, b, v)} > 0$. Let $A \in \mathbb{R}_{\ge 0}$ be a Lipschitz constant of `Real.smoothTransition`, $P \ge 1$ with `scalarCubePrimitiveEnvelope Empty A 1 0 q` $\le P$ and $\mathrm{step}_{(a_0, b, v)} \cdot q \le P$ for all $b, v$. Let $\varepsilon$ be real with `uniformSpectrumBlockCount j 1 deg` $\le |B_{a_0}|$, $0 < \varepsilon \le 1$, and $\sigma_j \le 1$.
--
--   **Conclusion.** Define (all functions explicit and defined by OpenAI): $V = \mathrm{torus} \cdot \mathrm{cost} / \delta^{\mathrm{deg}}$; $\zeta$ = `uniformBlockRetainedBias j 1 deg P V V ε`; $\mathrm{freq}$ = the nonnegative part of `uniformScaledRetainedFrequencyBound j 1 P V ζ`; $\mathrm{cap}$ = `uniformSpectrumAbsoluteCap j 1 deg P V V`; $R_0 = |\texttt{BoundedCoefficientExponent}\ K\ \mathrm{deg}| \cdot R_j$ with $K$ = `LayerSamplerVariables G I n B`; and $K_0 = \max\bigl(\texttt{allocatedSlicedGridHeightCutoff B j i}\ \lceil q/\delta \rceil,\ \mathrm{denom} \cdot 2^{\mathrm{deg}} \cdot H_{\mathrm{child}}^{\mathrm{deg}} + 2\,\mathrm{denom}\bigr)$ (a natural number). Then for every real $Q \ge 0$ with
--   $$R_0 + \tfrac14 \le e^{Q},\quad \Bigl(\frac{\varepsilon}{\mathrm{cap} + 1}\Bigr)^{-1} \le e^{Q},\quad \texttt{characterLipConstant} \cdot \mathrm{freq} + 4 \le e^{Q},\quad K_0 \le e^{Q},\quad 2K_0^3 \le e^{Q},\quad \varepsilon^{-1} \le e^{Q},$$
--   there is a `ScalarSiteExpansion` $e$ over $\mathrm{Finset}\,\emptyset$ (at universe level $0$; defined by OpenAI) such that:
--   1. `e.Bounds T D C L H` holds (defined by OpenAI: at most $T$ terms; all periods positive and at most $D$; total coefficient size at most $C$; every factor of absolute value at most $1$, $L$-Lipschitz, and vanishing for $|x| \ge H$) with
--      - $T = \max\bigl(\texttt{uniformSpectrumSizeConstant j 1 deg P V V} / \varepsilon^{\max(\texttt{majorArcSpectrumExponent j 1},\ \texttt{majorArcLengthExponent j} \cdot \mathrm{deg})} \cdot e^{4Q+8},\ e^{4Q+8}\bigr)$,
--      - $D = \max(\texttt{uniformScaledRetainedDenominatorBound j 1 deg P V V ζ}, 1)$,
--      - $C = \max(\mathrm{cap} \cdot e^{5Q+8}, e^{5Q+8})$,
--      - $L = e^{1 + 6Q + 12} + 4$,
--      - $H = R_0 + 1/4$;
--   2. for every $z \in \mathbb{Z}$,
--   $$\Bigl| h \cdot \pi(\underline{z}) - \texttt{e.integerEval}\ h\ (\_ \mapsto z) \Bigr| \le 2\varepsilon,$$
--      where $\pi$ = `allocatedSupportedSlicedResidueJetPMF B U basis hR hσ S q r H step c hH hsubset hcell j i univ (_ ↦ c₀)` is a probability mass function (defined by OpenAI) on functions from the rows ($\mathrm{univ} = \{\emptyset\}$) to $\mathbb{Z}$, $\underline{z}$ is the constant function with value $z$ (its mass is taken as a real number), and `e.integerEval h y` is $e$ evaluated at $y$ and at the real point $y/h$.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.exists_forecastInactive_sliced_fixed_zero_axis_site_small_or_dense_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.exists_forecastInactive_sliced_fixed_zero_axis_site_small_or_dense` (in `lean/OAI/Combinatorics/Progressions/Sampling/ForecastInactiveSlicedFixedProduct.lean`); the definitions it uses are in the definitions bundles `OAIE3v2B180`, `OAIE3v2B196` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Sampling/ForecastInactiveSlicedFixedProduct.lean (declaration OAI.Erdos3.VectorPolynomial.exists_forecastInactive_sliced_fixed_zero_axis_site_small_or_dense)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B180
import Definitions.Def_OAIE3v2B196

section

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
variable (q : ℕ) (hq : 0 < q) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option Empty → ZMod q)
variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ t, 0 < H t)
variable (hsubset : ∀ t, integerProgressionSupport (c t) (step t : ℤ) (H t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ))
variable (hcell : 0 < (principalTupleWeights (α := Empty) B (layerSamplerDegree I n) H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
variable (j : Fin m) (i : Fin (n j))

variable (Hchild : ℕ)

local notation "height" => basisAxisScale (basis j) i
local notation "degree" => Fin.val j + 1
local notation "denom" => inactiveDenominator
  (principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i)))
local notation "cost" => (denom : ℝ) * 2 ^ degree
local notation "torus" => blockTorusFactor (Fintype.card Empty) degree (Fintype.card (B (Sigma.mk j (Sum.inr i)))) 1

local notation "constantLaw" => allocatedLayerIntegerPMFs B U basis hR hσ S j i
  (principalCoefficientChoice (G := G) (layerSamplerDegree I n) (Sigma.mk j (Sum.inr i)) none)

include hq in
theorem exists_forecastInactive_sliced_fixed_zero_axis_site_small_or_dense_s2
    (c0 : ℤ) (hc0 : (constantLaw) c0 ≠ 0)
    (hgrid : allocatedGridAxis (I := I) U basis S.value ⟨j, Sum.inr i⟩)
    (hsmall : height ≤ S.value ^ degree)
    {δ : ℝ} (hδ : 0 < δ)
    (hreg : (∃ b0 v0,
      allocatedPrincipalSides B U basis S ⟨⟨j,Sum.inr i⟩,b0,v0⟩ < Hchild) ∨
      ((∀ b v, δ * allocatedPrincipalSides B U basis S ⟨⟨j,Sum.inr i⟩,b,v⟩ ≤
        (H ⟨⟨j,Sum.inr i⟩,b,v⟩ : ℝ)) ∧
       (∀ b v, 0 < step ⟨⟨j,Sum.inr i⟩,b,v⟩)))
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) (P : ℝ) (hP : 1 ≤ P)
    (hsP : scalarCubePrimitiveEnvelope Empty A 1 0 q ≤ P)
    (hstride : ∀ b v, ((step ⟨⟨j,Sum.inr i⟩,b,v⟩ * q : ℕ) : ℝ) ≤ P)
    {ε : ℝ}
    (hB : uniformSpectrumBlockCount j.val 1 degree ≤ Fintype.card (B ⟨j, Sum.inr i⟩))
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hσ1 : σ j ≤ 1) :
    let V := (torus : ℝ) * cost / δ ^ degree
    let ζ := uniformBlockRetainedBias j.val 1 degree P V V ε
    let freq := Real.toNNReal (uniformScaledRetainedFrequencyBound j.val 1 P V ζ)
    let cap := uniformSpectrumAbsoluteCap j.val 1 degree P V V
    let R0 := (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) degree) : ℝ) * R j
    let K := max (allocatedSlicedGridHeightCutoff (G := G) B (R := R) j i (Nat.ceil ((q : ℝ) / δ)))
      (denom * 2 ^ degree * Hchild ^ degree + 2 * denom)
    ∀ {Q : ℝ}, 0 ≤ Q → R0 + 1 / 4 ≤ Real.exp Q →
      (ε / (cap + 1))⁻¹ ≤ Real.exp Q →
      (CircleFourier.characterLipConstant * freq + 4 : ℝ≥0) ≤ Real.exp Q →
      (K : ℝ) ≤ Real.exp Q →
      (2 * (K : ℝ≥0) ^ 2 * (K : ℝ≥0) : ℝ≥0) ≤ Real.exp Q →
      ε⁻¹ ≤ Real.exp Q →
    ∃ e : ScalarSiteExpansion.{0,0} (Finset Empty),
      e.Bounds
        (max ((uniformSpectrumSizeConstant j.val 1 degree P V V /
          ε ^ max (majorArcSpectrumExponent j.val 1) (majorArcLengthExponent j.val * degree)) *
          Real.exp (4 * Q + 8)) (Real.exp (4 * Q + 8)))
        (max (uniformScaledRetainedDenominatorBound j.val 1 degree P V V ζ) 1)
        (max (cap * Real.exp (4 * Q + 8 + Q)) (Real.exp (4 * Q + 8 + Q)))
        (⟨Real.exp (1 + 6 * Q + 12), Real.exp_nonneg _⟩ + 4) (R0 + 1 / 4) ∧
      ∀ (z : ℤ),
        ‖(((height : ℝ) *
          (allocatedSupportedSlicedResidueJetPMF B U basis hR hσ S q r H step c hH hsubset hcell j i Finset.univ
            (fun _ => c0) (fun _ => z)).toReal : ℝ) : ℂ) - e.integerEval height (fun _ => z)‖ ≤ 2 * ε := by
  sorry

end Erdos3.VectorPolynomial

end

end OAI
end
