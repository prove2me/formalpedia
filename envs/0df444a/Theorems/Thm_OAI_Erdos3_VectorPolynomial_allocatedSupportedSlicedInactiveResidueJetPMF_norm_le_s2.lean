-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedSupportedSlicedInactiveResidueJetPMF_norm_le_s2
-- name    : OAI.Erdos3.VectorPolynomial.allocatedSupportedSlicedInactiveResidueJetPMF_norm_le_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T04:26:08.362118+00:00
-- url     : https://prove2.me/theorems/d48c282f-871a-4c0a-b393-bfca92393192
-- title:
--   The rescaled supported sliced residue jet PMF on an inactive integer axis is bounded by the uniform spectrum absolute cap
-- statement:
--   All named objects below are defined by OpenAI. Let $m$ be a natural number, $G$ a finite type, and for $j < m$ let $I_j$, $J_j$ be finite types and $n_j$ natural numbers; let $B_a$ be finite types indexed by `LayerSamplerAxis I n` (decidable equality is assumed on $I_j$ and $B_a$). For each $j$ let $U_j$ be a real subspace of $\mathbb{R}^{J_j}$ and `basis j` a basis, indexed by $\{0,\dots,n_j-1\}$, of the orthogonal complement of the Euclidean copy of $U_j$. Let $R_j, \sigma_j$ be real numbers with $R_j > 0$ and $\sigma_j > 0$ for all $j$, and let $S$ be a `LayerSamplerScale B U basis R σ` (with scale value `S.value`). Let $\alpha$ be a finite type with decidable equality. Write $\mathcal{T}$ for `PrincipalTupleIndex B (layerSamplerDegree I n)` (triples $(a, \beta, v)$ of an axis $a$, $\beta \in B_a$ and $v < $ `layerSamplerDegree I n a`). Let:
--   - $q$ be a natural number with $q > 0$, and $r : \mathcal{T} \to$ (`Option α` $\to \mathbb{Z}/q$) a residue pattern;
--   - $H, \mathrm{step} : \mathcal{T} \to \mathbb{N}$ and $c : \mathcal{T} \to \mathbb{Z}$ with $H(t) > 0$ for all $t$ (proof `hH`);
--   - `hsubset`: for every $t$, the progression `integerProgressionSupport (c t) (step t) (H t)` $= \{c(t) + \mathrm{step}(t)\,k : 0 \le k < H(t)\}$ is contained in $[0, \texttt{allocatedPrincipalSides B U basis S}\ t)$;
--   - `hcell`: the residue cell $\{y : y \bmod q = r\}$ (via `principalResidueLabel q`) has positive mass under `principalTupleWeights B (layerSamplerDegree I n) H hH`, the product of OpenAI's integer scalar cube weights with side lengths $H$;
--   - $j < m$ and $i < n_j$, with (`hsize`) $(|\alpha|+1)\,q \le H((j,\mathrm{inr}\ i), \beta, v)$ for all $\beta, v$.
--
--   Write $h$ = `basisAxisScale (basis j) i` (a natural number), $D = j+1$, $\mathrm{den}$ = `inactiveDenominator (principalProfileSize (R j) |layerIntegerPrincipalSlots B j i|)`, where `inactiveDenominator γ` $= \max(1, \lceil \gamma^{-1}\rceil)$ and `principalProfileSize R b` $= R/(8(b+1))$; side = `inactiveSideLength D h den` (equal to $\lfloor (h \operatorname{div} \mathrm{den})^{1/D}\rfloor$ if $2\,\mathrm{den} \le h$, and $1$ otherwise); cost $= \mathrm{den}\cdot 2^{D}$; and torus = `blockTorusFactor |α| D |B_{(j, inr i)}| 1`, a positive natural number.
--
--   Assume:
--   - $h \le \mathrm{S.value}^{D}$ and $2\,\mathrm{den} \le h$;
--   - $\delta > 0$ is real with $\delta \cdot \mathrm{side} \le H((j,\mathrm{inr}\ i), \beta, v)$ and $0 < \mathrm{step}((j,\mathrm{inr}\ i), \beta, v)$ for all $\beta, v$;
--   - $A$ is a nonnegative real such that `Real.smoothTransition` is $A$-Lipschitz; $P \ge 1$ is real with `scalarCubePrimitiveEnvelope α A 1 0 q` $\le P$ and $\mathrm{step}((j,\mathrm{inr}\ i), \beta, v)\cdot q \le P$ for all $\beta, v$;
--   - `rows` is a finite set of subsets of $\alpha$, each of cardinality at most $D$, with `uniformSpectrumBlockCount j |rows| (D |rows|)` $\le |B_{(j,\mathrm{inr}\ i)}|$;
--   - `shift` and $z$ are integer vectors indexed by `rows`.
--
--   Let $V = \mathrm{torus}\cdot\mathrm{cost}/\delta^{D}$, $t = D\,|\mathrm{rows}|$ and $W = (\mathrm{torus}\cdot\mathrm{cost})^{|\mathrm{rows}|}/\delta^{t}$. Then
--   $$\Bigl|h^{|\mathrm{rows}|}\cdot \texttt{allocatedSupportedSlicedResidueJetPMF B U basis hR hσ S q r H step c hH hsubset hcell j i rows shift}(z)\Bigr| \le \texttt{uniformSpectrumAbsoluteCap}\ j\ |\mathrm{rows}|\ t\ P\ V\ W,$$
--   where the PMF value is converted to a real number (and the left side is the norm of that real as a complex number); this PMF on $\mathbb{Z}^{\mathrm{rows}}$ is the law of $\mathrm{shift} + \sum_{\beta} \mathrm{coeff}_\beta \cdot (\text{Boolean block jet of } y \text{ on rows})$, with independent coefficients $\mathrm{coeff}_\beta$ drawn from `allocatedLayerIntegerPMFs B U basis hR hσ S j i` at the principal slots and $y$ drawn from OpenAI's conditioned supported principal-tuple law; and `uniformSpectrumAbsoluteCap` is an explicit constant of OpenAI.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.allocatedSupportedSlicedInactiveResidueJetPMF_norm_le_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.allocatedSupportedSlicedInactiveResidueJetPMF_norm_le` (in `lean/OAI/Combinatorics/Progressions/Geometry/AllocatedSupportedSlicedInactiveFixedCap.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B196` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Geometry/AllocatedSupportedSlicedInactiveFixedCap.lean (declaration OAI.Erdos3.VectorPolynomial.allocatedSupportedSlicedInactiveResidueJetPMF_norm_le)

import Mathlib
import Definitions.Def_ErdosReciprocal
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
variable {α : Type*} [Fintype α] [DecidableEq α]
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

local notation "torus" => blockTorusFactor (Fintype.card α) degree (Fintype.card (B (Sigma.mk j (Sum.inr i)))) 1

include hq hsize in

theorem allocatedSupportedSlicedInactiveResidueJetPMF_norm_le_s2
    (hsmall : height ≤ S.value ^ degree) (hlarge : 2 * denom ≤ height)
    {δ : ℝ} (hδ : 0 < δ)
    (hlength : ∀ b v, δ * side ≤ (H ⟨⟨j,Sum.inr i⟩,b,v⟩ : ℝ))
    (hstep : ∀ b v, 0 < step ⟨⟨j,Sum.inr i⟩,b,v⟩)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) (P : ℝ) (hP : 1 ≤ P)
    (hsP : scalarCubePrimitiveEnvelope α A 1 0 q ≤ P)
    (hstride : ∀ b v, ((step ⟨⟨j,Sum.inr i⟩,b,v⟩ * q : ℕ) : ℝ) ≤ P)
    (rows : Finset (Finset α)) (hrows : ∀ t ∈ rows, t.card ≤ degree)
    (hB : uniformSpectrumBlockCount j.val rows.card (degree * rows.card) ≤ Fintype.card (B ⟨j, Sum.inr i⟩))
    (shift z : rows → ℤ) :
    let V := (torus : ℝ) * cost / δ ^ degree
    let t := degree * rows.card
    let W := ((torus : ℝ) * cost) ^ rows.card / δ ^ t
    ‖(((height : ℝ) ^ rows.card *
      (allocatedSupportedSlicedResidueJetPMF B U basis hR hσ S q r H step c hH hsubset hcell j i rows shift z).toReal : ℝ) : ℂ)‖ ≤
      uniformSpectrumAbsoluteCap j.val rows.card t P V W := by
  sorry

end Erdos3.VectorPolynomial

end

end OAI
end
