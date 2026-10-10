-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_exists_forecastInactive_sliced_fixed_product_site
-- name    : OAI.Erdos3.VectorPolynomial.exists_forecastInactive_sliced_fixed_product_site
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-10T05:41:01.38974+00:00
-- url     : https://prove2.me/theorems/53f0b058-714e-497a-890b-69453d86260a
-- title:
--   A site expansion family approximates the product of shifted residue jet PMFs
-- statement:
--   Fix the section data: a natural number $m$; a finite type $G$; finite types $I_j$ with decidable equality and natural numbers $n_j$ ($j \in \mathrm{Fin}\,m$); finite types $B_a$ with decidable equality over the axes of `LayerSamplerAxis I n` (the sigma type $\Sigma_j\, I_j \oplus \mathrm{Fin}(n_j)$); finite types $J_j$, real subspaces $U_j \subseteq \mathbb R^{J_j}$ and bases `basis j` (indexed by $\mathrm{Fin}\,n_j$) of the orthogonal complements of `euclideanSubspace (U j)`; real functions $R, \sigma$ on $\mathrm{Fin}\,m$ with $R_j > 0$ (hR) and $\sigma_j > 0$ (hσ); a `LayerSamplerScale` $S$ (a structure bundling a positive natural number $S.\mathrm{value}$ with width and gap inequalities); $q \in \mathbb N$ with $q > 0$ (hq) and $r : \mathrm{FullInput} \to \mathrm{Option}\,\mathrm{Empty} \to \mathbb Z/q$, where FullInput $=$ `PrincipalTupleIndex B (layerSamplerDegree I n)`; $H, \mathrm{step} : \mathrm{FullInput} \to \mathbb N$ and $c : \mathrm{FullInput} \to \mathbb Z$ with $H_t > 0$ (hH) and each progression `integerProgressionSupport (c t) (step t) (H t)` $= \{c_t + \mathrm{step}_t k : 0 \le k < H_t\}$ contained in $[0,$ `allocatedPrincipalSides B U basis S t`$)$ (hsubset); the residue cell $\{y : \texttt{principalResidueLabel q y} = r\}$ of positive mass under `principalTupleWeights B (layerSamplerDegree I n) H hH` with $\alpha = \mathrm{Empty}$ (hcell); and a finite type $A$.
--
--   Let $\mathrm{selected} : A \to \Sigma_j\,\mathrm{Fin}(n_j)$; for $a \in A$ write $\langle j_a, i_a\rangle = \mathrm{selected}(a)$ and $x_a = \langle j_a, \mathrm{inr}\,i_a\rangle$. Let $\delta, P$ be reals and $H_{\mathrm{child}} \in \mathbb N$ with $\delta > 0$. Assume: for each $a$, either some $b_0, v_0$ have `allocatedPrincipalSides B U basis S ⟨x_a, b₀, v₀⟩` $< H_{\mathrm{child}}$, or else for all $b, v$ both $\delta\cdot$`allocatedPrincipalSides B U basis S ⟨x_a, b, v⟩` $\le H_{\langle x_a, b, v\rangle}$ and $\mathrm{step}_{\langle x_a,b,v\rangle} > 0$; `basisAxisScale (basis j_a) i_a` $\le S.\mathrm{value}^{j_a+1}$ and $x_a$ satisfies `allocatedGridAxis U basis S.value`, for all $a$; $c_0 : A \to \mathbb Z$ with $c_0(a)$ of nonzero probability under `allocatedLayerIntegerPMFs B U basis hR hσ S j_a i_a (principalCoefficientChoice (layerSamplerDegree I n) x_a none)` for all $a$; $\sigma_{j_a} \le 1$ for all $a$; $L \in \mathbb R_{\ge 0}$ with `Real.smoothTransition` $L$-Lipschitz; $1 \le P$ and `scalarCubePrimitiveEnvelope Empty L 1 0 q` $\le P$; $\mathrm{step}_{\langle x_a,b,v\rangle}\,q \le P$ for all $a, b, v$; and `uniformSpectrumBlockCount j_a 1 (j_a+1)` $\le |B_{x_a}|$ for all $a$. Let $C_{\mathrm{actual}}, \delta_{\mathrm{out}}, Q, N_t, V_t, C_t, H_t$ be reals and $L_t \in \mathbb R_{\ge 0}$ with $C_{\mathrm{actual}} \ge 0$, $\delta_{\mathrm{out}} > 0$, $Q \ge 0$.
--
--   Put, for each $a$: $\mathrm{degree}_a = j_a + 1$; $\mathrm{height}_a =$ `basisAxisScale (basis j_a) i_a`; $\mathrm{denom}_a =$ `inactiveDenominator (principalProfileSize (R j_a) |layerIntegerPrincipalSlots B j_a i_a|)`; $\mathrm{torus}_a =$ `blockTorusFactor 0 degree_a |B x_a| 1`; $V_a = \mathrm{torus}_a\cdot\mathrm{denom}_a 2^{\mathrm{degree}_a}/\delta^{\mathrm{degree}_a}$; $\mathrm{cap}_a =$ `uniformSpectrumAbsoluteCap j_a 1 degree_a P V_a V_a`; $\mathrm{cutoff}_a = \max(\texttt{allocatedSlicedGridHeightCutoff B j_a i_a}\lceil q/\delta\rceil,\ \mathrm{denom}_a 2^{\mathrm{degree}_a}H_{\mathrm{child}}^{\mathrm{degree}_a} + 2\,\mathrm{denom}_a)$; $R_{0,a} = |\texttt{BoundedCoefficientExponent (LayerSamplerVariables G I n B) degree_a}|\cdot R_{j_a}$; $\varepsilon =$ `uniformProductAccuracy |A| Cactual δout` $/2$; $\zeta_a =$ `uniformBlockRetainedBias j_a 1 degree_a P V_a V_a ε`; and $\mathrm{freq}_a =$ `uniformScaledRetainedFrequencyBound j_a 1 P V_a ζ_a` (made nonnegative). Assume further, for all $a$: $\max(\mathrm{cutoff}_a, \mathrm{cap}_a) \le C_{\mathrm{actual}}$; $R_{0,a} + 1/4 \le e^Q$; $(\varepsilon/(\mathrm{cap}_a + 1))^{-1} \le e^Q$; $\texttt{CircleFourier.characterLipConstant}\cdot\mathrm{freq}_a + 4 \le e^Q$; $\mathrm{cutoff}_a \le e^Q$; $2\,\mathrm{cutoff}_a^3 \le e^Q$; $\max\bigl((\texttt{uniformSpectrumSizeConstant j_a 1 degree_a P V_a V_a}/\varepsilon^{\max(\texttt{majorArcSpectrumExponent j_a 1},\ \texttt{majorArcLengthExponent j_a}\cdot\mathrm{degree}_a)})e^{4Q+8},\ e^{4Q+8}\bigr) \le N_t$; $\max(\texttt{uniformScaledRetainedDenominatorBound j_a 1 degree_a P V_a V_a ζ_a}, 1) \le V_t$; $\max(\mathrm{cap}_a e^{5Q+8}, e^{5Q+8}) \le C_t$; and $R_{0,a} + 1/4 \le H_t$; and also $\varepsilon^{-1} \le e^Q$ and $\exp(1+6Q+12) + 4 \le L_t$.
--
--   Then there is a family $e$ of `ScalarSiteExpansion`s on $\mathrm{Finset}\,\mathrm{Empty}$ indexed by $A$ (each a finite family of terms with periods, complex coefficients and factors $\mathbb Z/p \times \mathbb R \to \mathbb C$) with `(e a).Bounds Nt Vt Ct Lt Ht` for every $a$ (at most $N_t$ terms, periods in $(0, V_t]$, coefficient norms summing to at most $C_t$, factors of norm at most $1$, $L_t$-Lipschitz in the real argument, vanishing at real arguments $x$ with $|x| \ge H_t$), such that for every $z : A \to \mathbb Z$,
--   $$\Bigl\|\Bigl(\prod_a \mathrm{height}_a\Bigr)\cdot\Pi\bigl(a \mapsto (\_ \mapsto z_a)\bigr) - \texttt{siteFamilyEval}\ e\ (\_ \mapsto z)\ \bigl(\_, a \mapsto z_a/\mathrm{height}_a\bigr)\Bigr\| \le \delta_{\mathrm{out}},$$
--   where $\Pi$ is the product PMF (`dependentProductPMF`) over $a$ of `allocatedSupportedSlicedResidueJetPMF B U basis hR hσ S q r H step c hH hsubset hcell j_a i_a univ (fun _ => c₀ a)` (each a PMF on functions from the one-element set of finsets of Empty to $\mathbb Z$).
--
--   Lean: `OAI.Erdos3.VectorPolynomial.exists_forecastInactive_sliced_fixed_product_site` in `lean/OAI/Combinatorics/Progressions/Sampling/ForecastInactiveSlicedFixedProduct.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B055`, `OAIErdos3B145` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Sampling/ForecastInactiveSlicedFixedProduct.lean#L307

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B055
import Definitions.Def_OAIErdos3B145

namespace OAI

section

namespace Erdos3.VectorPolynomial

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
variable (q : ℕ) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) (allocatedPrincipalSides_pos B U basis S)).mass
    (Finset.univ.filter (fun y => principalResidueLabel q y = r)))

local notation "conditioned" => FiniteProbabilityWeights.condition
  (principalTupleWeights B (layerSamplerDegree I n)
    (allocatedPrincipalSides B U basis S) (allocatedPrincipalSides_pos B U basis S))
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)) hcell

variable {A : Type*} [Fintype A]
variable (selected : A → Σ j : Fin m, Fin (n j))
variable (rows : A → Finset (Finset α)) (x : G → IntegerScalarCubeBox α S.value)

variable (hselected : Function.Injective selected)
variable (hgrid : ∀ a, allocatedGridAxis (I := I) U basis S.value
  ⟨(selected a).1, Sum.inr (selected a).2⟩)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

universe uα

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (q : ℕ) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
    (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
variable {A : Type*} [Fintype A]
variable (selected : A → Σ j : Fin m, Fin (n j)) (rows : A → Finset (Finset α))

end Erdos3.VectorPolynomial

end

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
local notation "side" => inactiveSideLength degree height denom
local notation "cost" => (denom : ℝ) * 2 ^ degree
local notation "radius" => blockJetScaleBound (Fintype.card Empty) degree (Fintype.card (B (Sigma.mk j (Sum.inr i)))) 1
local notation "torus" => blockTorusFactor (Fintype.card Empty) degree (Fintype.card (B (Sigma.mk j (Sum.inr i)))) 1

local notation "constantLaw" => allocatedLayerIntegerPMFs B U basis hR hσ S j i
  (principalCoefficientChoice (G := G) (layerSamplerDegree I n) (Sigma.mk j (Sum.inr i)) none)

end Erdos3.VectorPolynomial

end

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
variable {A : Type*} [Fintype A]

include hq in
theorem exists_forecastInactive_sliced_fixed_product_site
    (selected : A → Σ j : Fin m, Fin (n j))
    (δ P : ℝ) (Hchild : ℕ) (hδ : 0 < δ)
    (hreg : ∀ a, (∃ b0 v0,
      allocatedPrincipalSides B U basis S ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b0,v0⟩ < Hchild) ∨
      ((∀ b v, δ * allocatedPrincipalSides B U basis S ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b,v⟩ ≤
        (H ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b,v⟩ : ℝ)) ∧
       (∀ b v, 0 < step ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b,v⟩)))
    (hsmall : ∀ a, basisAxisScale (basis (selected a).1) (selected a).2 ≤
      S.value ^ ((selected a).1.val + 1))
    (hgrid : ∀ a, allocatedGridAxis (I := I) U basis S.value ⟨(selected a).1, Sum.inr (selected a).2⟩)
    (c0 : A → ℤ)
    (hc0 : ∀ a, allocatedLayerIntegerPMFs B U basis hR hσ S (selected a).1 (selected a).2
      (principalCoefficientChoice (G := G) (layerSamplerDegree I n)
        ⟨(selected a).1, Sum.inr (selected a).2⟩ none) (c0 a) ≠ 0)
    (hσ1 : ∀ a, σ (selected a).1 ≤ 1)
    (L : ℝ≥0) (hL : LipschitzWith L Real.smoothTransition)
    (hP : 1 ≤ P) (hsP : scalarCubePrimitiveEnvelope Empty L 1 0 q ≤ P)
    (hstride : ∀ a b v, ((step ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b,v⟩ * q : ℕ) : ℝ) ≤ P)
    (hB : ∀ a, uniformSpectrumBlockCount (selected a).1.val 1 ((selected a).1.val + 1) ≤
      Fintype.card (B ⟨(selected a).1, Sum.inr (selected a).2⟩))
    (Cactual δout Q Nt Vt Ct Ht : ℝ) (Lt : ℝ≥0)
    (hCactual : 0 ≤ Cactual) (hδout : 0 < δout) (hQ : 0 ≤ Q) :
    let degree := fun a => (selected a).1.val + 1
    let height := fun a => basisAxisScale (basis (selected a).1) (selected a).2
    let denom := fun a => inactiveDenominator (principalProfileSize (R (selected a).1)
      (Finset.card (layerIntegerPrincipalSlots (G := G) B (selected a).1 (selected a).2)))
    let torus := fun a => blockTorusFactor (Fintype.card Empty) (degree a)
      (Fintype.card (B ⟨(selected a).1, Sum.inr (selected a).2⟩)) 1
    let V := fun a => (torus a : ℝ) * ((denom a : ℝ) * 2 ^ degree a) / δ ^ degree a
    let cap := fun a => uniformSpectrumAbsoluteCap (selected a).1.val 1 (degree a) P (V a) (V a)
    let cutoff := fun a => max (allocatedSlicedGridHeightCutoff (G := G) B (R := R)
      (selected a).1 (selected a).2 (Nat.ceil ((q : ℝ) / δ)))
      (denom a * 2 ^ degree a * Hchild ^ degree a + 2 * denom a)
    let R0 := fun a => (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (degree a)) : ℝ) *
      R (selected a).1
    let ε := uniformProductAccuracy (Fintype.card A) Cactual δout / 2
    let ζ := fun a => uniformBlockRetainedBias (selected a).1.val 1 (degree a) P (V a) (V a) ε
    let freq := fun a => Real.toNNReal (uniformScaledRetainedFrequencyBound (selected a).1.val 1 P (V a) (ζ a))
    (∀ a, max (cutoff a : ℝ) (cap a) ≤ Cactual) →
    (∀ a, R0 a + 1 / 4 ≤ Real.exp Q) →
    (∀ a, (ε / (cap a + 1))⁻¹ ≤ Real.exp Q) →
    (∀ a, (CircleFourier.characterLipConstant * freq a + 4 : ℝ≥0) ≤ Real.exp Q) →
    (∀ a, (cutoff a : ℝ) ≤ Real.exp Q) →
    (∀ a, (2 * (cutoff a : ℝ≥0) ^ 2 * (cutoff a : ℝ≥0) : ℝ≥0) ≤ Real.exp Q) →
    ε⁻¹ ≤ Real.exp Q →
    (∀ a, max ((uniformSpectrumSizeConstant (selected a).1.val 1 (degree a) P (V a) (V a) /
      ε ^ max (majorArcSpectrumExponent (selected a).1.val 1)
        (majorArcLengthExponent (selected a).1.val * degree a)) * Real.exp (4 * Q + 8))
      (Real.exp (4 * Q + 8)) ≤ Nt) →
    (∀ a, max (uniformScaledRetainedDenominatorBound (selected a).1.val 1 (degree a) P
      (V a) (V a) (ζ a)) 1 ≤ Vt) →
    (∀ a, max (cap a * Real.exp (4 * Q + 8 + Q)) (Real.exp (4 * Q + 8 + Q)) ≤ Ct) →
    (⟨Real.exp (1 + 6 * Q + 12), Real.exp_nonneg _⟩ + 4 : ℝ≥0) ≤ Lt →
    (∀ a, R0 a + 1 / 4 ≤ Ht) →
    ∃ e : A → ScalarSiteExpansion.{0,0} (Finset Empty),
      (∀ a, (e a).Bounds Nt Vt Ct Lt Ht) ∧
      ∀ z : A → ℤ,
        ‖(((∏ a, (height a : ℝ)) *
          (dependentProductPMF (fun a => allocatedSupportedSlicedResidueJetPMF B U basis hR hσ S q r
            H step c hH hsubset hcell (selected a).1 (selected a).2 (Finset.univ : Finset (Finset Empty))
            (fun _ => c0 a)) (fun a _ => z a)).toReal : ℝ) : ℂ) -
          siteFamilyEval e (fun _ => z) (fun _ a => (z a : ℝ) / height a)‖ ≤ δout := by
  sorry

end Erdos3.VectorPolynomial
end
end OAI
