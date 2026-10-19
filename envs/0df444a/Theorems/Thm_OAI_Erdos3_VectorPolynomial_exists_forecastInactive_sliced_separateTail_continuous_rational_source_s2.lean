-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_exists_forecastInactive_sliced_separateTail_continuous_rational_source_s2
-- name    : OAI.Erdos3.VectorPolynomial.exists_forecastInactive_sliced_separateTail_continuous_rational_source_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T04:31:29.988161+00:00
-- url     : https://prove2.me/theorems/faa10579-2c6b-4ecb-a9b3-efc9d380a207
-- title:
--   A bounded site expansion of the rational inactive forecast, with separate grid-tail and character-decay errors
-- statement:
--   Let $m$ be a natural number and $G$ a finite type. For each $j < m$ let $I_j$ be a finite type with decidable equality, $n_j$ a natural number, $J_j$ a finite type, $U_j$ a real subspace of $\mathbb{R}^{J_j}$ with Euclidean subspace $V_j$, and $\mathrm{basis}_j$ a real basis of $V_j^{\perp}$ indexed by $\{0,\dots,n_j-1\}$. For each layer sampler axis $a$ (OpenAI's `LayerSamplerAxis I n`: pairs $(j, c)$ with $c \in I_j \sqcup \{0,\dots,n_j-1\}$; the axis $(j,c)$ has degree $j+1$) let $B_a$ be a finite type with decidable equality. Let $R, \sigma : \{0,\dots,m-1\} \to \mathbb{R}$ with $R_j, \sigma_j > 0$, and let $S$ be a layer sampler scale (OpenAI's `LayerSamplerScale B U basis R σ`, main field `S.value`). The principal indices are the triples $(a, b, v)$ with $a$ an axis, $b \in B_a$, $v < \deg a$; let $\mathrm{side}$ = `allocatedPrincipalSides B U basis S` (OpenAI side lengths). Let $H, \mathrm{step}$ be natural-number functions and $c$ an integer function of the principal index, with $H > 0$ and each progression $\{c + \mathrm{step}\,k : k < H\}$ contained in $\{0,\dots,\mathrm{side} - 1\}$. Let $A$, $V_{\mathrm{act}}$ and $\mathrm{Out}$ be finite types (the last two with decidable equality).
--
--   **Hypotheses.** Let $\mathrm{selected} : A \to \{(j, i) : j < m,\ i < n_j\}$ be injective; for $a \in A$ write $(j_a, i_a) = \mathrm{selected}(a)$, $\bar a = (j_a, i_a)$ for the corresponding integer axis and $h_a$ = `basisAxisScale (basis j_a) i_a` $= \lceil 1/\lVert \mathrm{basis}_{j_a}(i_a)\rVert\rceil$. Let $\mathrm{poly}$ assign to each $o \in \mathrm{Out}$ an integer polynomial in variables indexed by $V_{\mathrm{act}} \sqcup (\text{principal indices} \times \mathrm{Option}\,\varnothing)$. Let $N$ be a nonzero natural number, $p_{\mathrm{Rat}}$ probability weights on $(\mathbb{Z}/N)^{V_{\mathrm{act}}}$, $T > 0$ a natural number, $\delta > 0$ and $P$ reals, and $H_{\mathrm{child}}$ a natural number. Assume:
--   - for every $a$: either some $\mathrm{side}_{(\bar a, b_0, v_0)} < H_{\mathrm{child}}$, or ($\delta\,\mathrm{side}_{(\bar a,b,v)} \le H_{(\bar a,b,v)}$ and $\mathrm{step}_{(\bar a,b,v)} > 0$ for all $b, v$);
--   - $h_a \le \texttt{S.value}^{j_a+1}$ and `allocatedGridAxis U basis S.value` holds at $\bar a$ for every $a$;
--   - for each $a$, integer coefficients $\mathrm{coefficients}_a(d)$ indexed by the exponent vectors $d$ of total degree $\le j_a+1$ in the layer sampler variables, each in the support of OpenAI's allocated layer integer law `allocatedLayerIntegerPMFs B U basis hR hσ S j_a i_a d`;
--   - $\sigma_{j_a} \le 1$ for all $a$; $L \ge 0$ with `Real.smoothTransition` $L$-Lipschitz; $1 \le P$, `scalarCubePrimitiveEnvelope Empty L 1 0 T` $\le P$, $\mathrm{step}_{(\bar a,b,v)}\,T \le P$; `uniformSpectrumBlockCount j_a 1 (j_a+1)` $\le |B_{\bar a}|$;
--   - reals $C_{\mathrm{actual}} \ge 0$, $\delta_{\mathrm{out}} > 0$, $Q \ge 0$, $N_t$, $V_t$, $C_t \ge 0$, $H_t$ and $L_t \ge 0$ such that `forecastInactiveSlicedSiteNumerics B selected q H_child δ P C_actual δ_out Q N_t V_t C_t H_t L_t` holds for every natural number $q$ with $0 < q \le T$ (an OpenAI proposition);
--   - reals $P_{\mathrm{tail}} \ge 1$ and $C_{\mathrm{tail}} \ge 0$ with `scalarCubePrimitiveEnvelope Empty L 1 0 1` $\le P_{\mathrm{tail}}$, $\mathrm{step}_{(\bar a,b,v)} \le P_{\mathrm{tail}}$, and for every $a$, with $\mathrm{deg} = j_a + 1$, $\mathrm{denom}$ = `inactiveDenominator (principalProfileSize R_{j_a} k_a)` $= \max(1, \lceil 8(k_a + 1)/R_{j_a}\rceil)$ where $k_a$ is the number of elements of `layerIntegerPrincipalSlots B j_a i_a`, $\mathrm{torus}$ = `blockTorusFactor 0 deg |B_ā| 1`, $V' = \mathrm{torus}\cdot\mathrm{denom}\,2^{\mathrm{deg}}/\delta^{\mathrm{deg}}$ and $\mathrm{cutoff} = \max\bigl(\texttt{allocatedSlicedGridHeightCutoff B j_a i_a}\ \lceil 1/\delta\rceil,\ \mathrm{denom}\,2^{\mathrm{deg}} H_{\mathrm{child}}^{\mathrm{deg}} + 2\,\mathrm{denom}\bigr)$: $\max(\mathrm{cutoff},\ \texttt{uniformSpectrumAbsoluteCap}\ j_a\ 1\ \mathrm{deg}\ P_{\mathrm{tail}}\ V'\ V') \le C_{\mathrm{tail}}$ (OpenAI quantities);
--   - reals $C_{\mathrm{decay}} \ge 0$ and $P_{\mathrm{decay}} \ge |\mathrm{Out}| + 2$ such that for every principal tuple $y$ (with $\alpha$ empty and sides $\mathrm{side}$) and every additive character $\chi$ of $(\mathbb{Z}/N)^{\mathrm{Out}}$,
--   $$\Bigl|\,\mathbb{E}_{t \sim p_{\mathrm{Rat}}}\, \chi\bigl((\mathrm{poly}_o(t, y) \bmod N)_{o}\bigr)\Bigr| \le C_{\mathrm{decay}}\,\operatorname{ord}(\chi)^{-P_{\mathrm{decay}}},$$
--   where $\mathrm{poly}_o(t, y)$ = `integerLongPolynomialOutput poly y N t o` evaluates $\mathrm{poly}_o$ at the canonical representatives of $t$ and the integer entries of $y$;
--   - a pseudometric space $\mathcal{Y}$ and a function $\mathrm{density} : \mathcal{Y} \to \mathbb{R}$ with $|\mathrm{density}| \le H_d$ for a real $H_d \ge 1$, and $\mathrm{density}$ Lipschitz with constant $L_d \ge 0$.
--
--   **Conclusion.** Let $p$ = `principalTupleWeights B (layerSamplerDegree I n) H hH` (OpenAI's product of integer scalar cube weights with lengths $H$), $\mathrm{law}$ its image under OpenAI's `containedProgressionTupleMap` (determined by $\mathrm{side}$, $H$, $\mathrm{step}$, $c$), $\mathrm{Ch}$ the set of characters $\chi$ of $(\mathbb{Z}/N)^{\mathrm{Out}}$ with $\operatorname{ord}(\chi) \le T$, and for $\chi \in \mathrm{Ch}$ let $\mathrm{Pos}(\chi)$ be the set of residue labels $r$ modulo $\operatorname{ord}(\chi)$ whose residue cell has positive $p$-mass. For $r \in \mathrm{Pos}(\chi)$ let $\mathrm{weight}(\chi, r) = p(\text{cell of } r)\cdot$`forecastInactiveCharacterCoefficient poly N p_Rat χ (progressionPrincipalResidue … step c (ord χ) r)` (OpenAI). Then there is a family $e(\chi, r, a)$ of OpenAI `ScalarSiteExpansion`s over the subsets of the empty type (each a finite set of terms $\theta$ with periods $\mathrm{per}(\theta)$, coefficients and factors) such that every $e(\chi, r, a)$ satisfies OpenAI's `Bounds N_t V_t C_t L_t H_t`, and, letting a term $\tau$ be a triple $(\chi, r, (\theta_a)_{a \in A})$ with $\theta_a$ a term of $e(\chi, r, a)$, $\mathrm{coeff}(\tau) = H_d\cdot$`forecastSiteMixtureCoefficient (e χ) (weight χ) (r, θ)`, and
--   $$\mathrm{factor}(w, \tau, z, (y, s)) = \overline{\chi(w)}\cdot\frac{\mathrm{density}(y)}{H_d}\cdot\texttt{siteFamilyFactor}\ (e(\chi, r))\ \theta\ \varnothing\ \bigl(a \mapsto z_a \bmod \mathrm{per}(\theta_a)\bigr)\ s$$
--   for $w \in (\mathbb{Z}/N)^{\mathrm{Out}}$, $z \in \mathbb{Z}^{A}$, $y \in \mathcal{Y}$, $s \in \mathbb{R}^{A}$:
--   1. $\sum_\tau |\mathrm{coeff}(\tau)| \le H_d\, T^{|\mathrm{Out}|+1} C_t^{|A|}$;
--   2. $|\mathrm{factor}(w, \tau, z, (y, s))| \le 1$ always;
--   3. for fixed $w, \tau, z$, the map $(y, s) \mapsto \mathrm{factor}(w, \tau, z, (y, s))$ is Lipschitz with constant $L_d + |A|\,L_t$;
--   4. for every $x : G \to$ `IntegerScalarCubeBox Empty S.value`, $z \in \mathbb{Z}^{A}$, $w \in (\mathbb{Z}/N)^{\mathrm{Out}}$ and $y \in \mathcal{Y}$,
--   $$\Bigl|\mathrm{density}(y)\cdot\mathcal{F}(x, z, w) - \sum_\tau \mathrm{coeff}(\tau)\,\mathrm{factor}\bigl(w, \tau, z, (y, (z_a/h_a)_a)\bigr)\Bigr| \le H_d\bigl(C_{\mathrm{tail}}^{|A|}\,C_{\mathrm{decay}}/T + T^{|\mathrm{Out}|+1}\,\delta_{\mathrm{out}}\bigr),$$
--   where $\mathcal{F}(x, z, w)$ = `rationalInactiveForecast law (fun _ => p_Rat) (forecastInactiveFixedOutput B U basis S selected coefficients x) (poly outputs) N (∏_a h_a) (a ↦ z_a) w` is OpenAI's rational inactive forecast: $\prod_a h_a$ times the $\mathrm{law}$-expectation over $y'$ of $\mathbf{1}\{\texttt{forecastInactiveFixedOutput}\ \ldots\ x\ y' = (a \mapsto z_a)\}$ times $N^{|\mathrm{Out}|}$ times the $p_{\mathrm{Rat}}$-probability that $(\mathrm{poly}_o(t, y') \bmod N)_o = w$ (an unnormalized fiber mean, not a conditional expectation).
--
--   Lean: `OAI.Erdos3.VectorPolynomial.exists_forecastInactive_sliced_separateTail_continuous_rational_source_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.exists_forecastInactive_sliced_separateTail_continuous_rational_source` (in `lean/OAI/Combinatorics/Progressions/Sampling/ActualSlicedForecastLateData.lean`); the definitions it uses are in the definitions bundles `OAIE3v2B180`, `OAIE3v2B197` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Sampling/ActualSlicedForecastLateData.lean (declaration OAI.Erdos3.VectorPolynomial.exists_forecastInactive_sliced_separateTail_continuous_rational_source)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B180
import Definitions.Def_OAIE3v2B197

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
variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ t, 0 < H t)
variable (hsubset : ∀ t, integerProgressionSupport (c t) (step t : ℤ) (H t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ))
variable {A : Type*} [Fintype A]
attribute [local instance] ScalarSiteExpansion.termFinite

variable {Vact Out : Type*} [Fintype Vact] [DecidableEq Vact] [Fintype Out] [DecidableEq Out]

attribute [local instance] OAI.Erdos3.VectorPolynomial.instNeZeroNatOrderOfAddCharForallZModComplex_9
theorem exists_forecastInactive_sliced_separateTail_continuous_rational_source_s2
    (selected : A → Σ j : Fin m, Fin (n j))
    (hselected : Function.Injective selected)
    (poly : Out → MvPolynomial (Vact ⊕ (PrincipalTupleIndex B (layerSamplerDegree I n) × Option Empty)) ℤ)
    (N : ℕ) [NeZero N] (pRat : FiniteProbabilityWeights (Vact → ZMod N))
    (T : ℕ) (hT : 0 < T)
    (δ P : ℝ) (Hchild : ℕ) (hδ : 0 < δ)
    (hreg : ∀ a, (∃ b0 v0,
      allocatedPrincipalSides B U basis S ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b0,v0⟩ < Hchild) ∨
      ((∀ b v, δ * allocatedPrincipalSides B U basis S ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b,v⟩ ≤
        (H ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b,v⟩ : ℝ)) ∧
       (∀ b v, 0 < step ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b,v⟩)))
    (hsmall : ∀ a, basisAxisScale (basis (selected a).1) (selected a).2 ≤
      S.value ^ ((selected a).1.val + 1))
    (hgrid : ∀ a, allocatedGridAxis (I := I) U basis S.value ⟨(selected a).1, Sum.inr (selected a).2⟩)
    (coefficients : ∀ a, BoundedCoefficientExponent (LayerSamplerVariables G I n B)
      ((selected a).1.val + 1) → ℤ)
    (hcoefficients : ∀ a d, coefficients a d ∈ (allocatedLayerIntegerPMFs B U basis hR hσ S
      (selected a).1 (selected a).2 d).support)
    (hσ1 : ∀ a, σ (selected a).1 ≤ 1)
    (L : ℝ≥0) (hL : LipschitzWith L Real.smoothTransition)
    (hP : 1 ≤ P) (hsP : scalarCubePrimitiveEnvelope Empty L 1 0 T ≤ P)
    (hstride : ∀ a b v, ((step ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b,v⟩ * T : ℕ) : ℝ) ≤ P)
    (hB : ∀ a, uniformSpectrumBlockCount (selected a).1.val 1 ((selected a).1.val + 1) ≤
      Fintype.card (B ⟨(selected a).1, Sum.inr (selected a).2⟩))
    (Cactual δout Q Nt Vt Ct Ht : ℝ) (Lt : ℝ≥0)
    (hCactual : 0 ≤ Cactual) (hCtNonneg : 0 ≤ Ct) (hδout : 0 < δout) (hQ : 0 ≤ Q)
    (hnumerics : ∀ q : ℕ, 0 < q → q ≤ T →
      forecastInactiveSlicedSiteNumerics (G := G) B (R := R) selected q Hchild
        δ P Cactual δout Q Nt Vt Ct Ht Lt)
    (Ptail Ctail : ℝ) (hPtail : 1 ≤ Ptail)
    (hsPtail : scalarCubePrimitiveEnvelope Empty L 1 0 1 ≤ Ptail)
    (hstrideTail : ∀ a b v,
      (step ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b,v⟩ : ℝ) ≤ Ptail)
    (hCtail : 0 ≤ Ctail)
    (htailactual : ∀ a,
      let degree := (selected a).1.val + 1
      let denom := inactiveDenominator (principalProfileSize (R (selected a).1)
        (Finset.card (layerIntegerPrincipalSlots (G := G) B (selected a).1 (selected a).2)))
      let torus := blockTorusFactor (Fintype.card Empty) degree
        (Fintype.card (B ⟨(selected a).1, Sum.inr (selected a).2⟩)) 1
      let V := (torus : ℝ) * ((denom : ℝ) * 2 ^ degree) / δ ^ degree
      let cutoff := max (allocatedSlicedGridHeightCutoff (G := G) B (R := R)
        (selected a).1 (selected a).2 (Nat.ceil ((1 : ℝ) / δ)))
        (denom * 2 ^ degree * Hchild ^ degree + 2 * denom)
      max (cutoff : ℝ)
        (uniformSpectrumAbsoluteCap (selected a).1.val 1 degree Ptail V V) ≤ Ctail)
    {Cdecay Pdecay : ℝ} (hCdecay : 0 ≤ Cdecay)
    (hPdecay : ((Fintype.card Out + 2 : ℕ) : ℝ) ≤ Pdecay)
    (hdecay : ∀ (y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
        (allocatedPrincipalSides B U basis S)) (χ : AddChar (Out → ZMod N) ℂ),
      ‖finiteImageCharacteristic pRat
        (fun t j => (integerLongPolynomialOutput poly (fun k => (y k.1 k.2 : ℤ)) N t j : ZMod N)) χ‖ ≤
        Cdecay * (orderOf χ : ℝ) ^ (-Pdecay))
    {SmoothCoord : Type*} [PseudoMetricSpace SmoothCoord]
    (density : SmoothCoord → ℝ) (Hdensity : ℝ) (hHdensity : 1 ≤ Hdensity)
    (hdensity : ∀ y, ‖density y‖ ≤ Hdensity)
    (densityLip : ℝ≥0) (hdensityLip : LipschitzWith densityLip density) :
    let p := principalTupleWeights (α := Empty) B (layerSamplerDegree I n) H hH
    let map := containedProgressionTupleMap B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U basis S) H step c (allocatedPrincipalSides_pos B U basis S) hsubset
    let law := p.fiberLaw map
    let Ch := Finset.univ.filter (fun χ : AddChar (Out → ZMod N) ℂ => orderOf χ ≤ T)
    let Pos := fun χ : Ch =>
      {r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option Empty → ZMod (orderOf χ.val) //
        0 < p.mass (Finset.univ.filter (fun y => principalResidueLabel (orderOf χ.val) y = r))}
    letI : ∀ χ : Ch, Fintype (Pos χ) := fun χ => by
      dsimp only [Pos]
      infer_instance
    let height := fun a => basisAxisScale (basis (selected a).1) (selected a).2
    let weight := fun (χ : Ch) (r : Pos χ) =>
      (p.mass (Finset.univ.filter (fun y => principalResidueLabel (orderOf χ.val) y = r.val)) : ℂ) *
        forecastInactiveCharacterCoefficient poly N pRat χ.val
          (progressionPrincipalResidue B (layerSamplerDegree I n) step c (orderOf χ.val) r.val)
    ∃ e : ∀ χ : Ch, Pos χ → A → ScalarSiteExpansion.{0,0} (Finset Empty),
      (∀ χ r a, (e χ r a).Bounds Nt Vt Ct Lt Ht) ∧
      let Term := Σ χ : Ch, Σ r : Pos χ, ∀ a, (e χ r a).Term
      let coeff := fun t : Term => (Hdensity : ℂ) * forecastSiteMixtureCoefficient (e t.1) (weight t.1) t.2
      let factor := fun (outPoint : Out → ZMod N) (t : Term) (z : A → ℤ)
          (y : SmoothCoord × (A → ℝ)) =>
        (star (t.1.val outPoint) * ((density y.1 : ℂ) / (Hdensity : ℂ))) *
          siteFamilyFactor (e t.1 t.2.1) t.2.2 ∅
            (fun a => (z a : ZMod ((e t.1 t.2.1 a).period (t.2.2 a)))) y.2
      (∑ t : Term, ‖coeff t‖) ≤ Hdensity * ((T : ℝ) ^ (Fintype.card Out + 1) * Ct ^ Fintype.card A) ∧
      (∀ outPoint t z y, ‖factor outPoint t z y‖ ≤ 1) ∧
      (∀ outPoint t z, LipschitzWith (densityLip + Fintype.card A * Lt) (factor outPoint t z)) ∧
      ∀ (x : G → IntegerScalarCubeBox Empty S.value) (z : A → ℤ)
          (outPoint : Out → ZMod N) (y : SmoothCoord),
        ‖(density y : ℂ) * (rationalInactiveForecast law (fun _ => pRat)
          (forecastInactiveFixedOutput B U basis S selected coefficients x)
          (fun y t j => integerLongPolynomialOutput poly (fun k => (y k.1 k.2 : ℤ)) N t j)
          N (∏ a, (height a : ℝ)) (fun a _ => z a) outPoint : ℂ) -
          ∑ t : Term, coeff t * factor outPoint t z (y, fun a => (z a : ℝ) / height a)‖ ≤
          Hdensity * (Ctail ^ Fintype.card A * (Cdecay / T) +
            (T : ℝ) ^ (Fintype.card Out + 1) * δout) := by
  sorry

end Erdos3.VectorPolynomial

end

end OAI
end
