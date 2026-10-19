-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_forecastJointOriginalGridMean_comparison_s2
-- name    : OAI.Erdos3.VectorPolynomial.forecastJointOriginalGridMean_comparison_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T04:51:58.845402+00:00
-- url     : https://prove2.me/theorems/dd89d15c-a083-4c66-9d8f-a91fe43198e8
-- title:
--   Comparison of the forecast joint original grid mean with the rational inactive forecast expansion
-- statement:
--   **Setup.** Let $X$ be a finite type, $m$ a positive natural number ($hm$), $I_j$, $E_j$, $J_j$ ($j < m$) finite types, $n_j$ natural numbers, $U_j \subseteq \mathbb{R}^{J_j}$ subspaces, `basis j` bases (indexed by $\{0,\dots,n_j-1\}$) of the orthogonal complement of $U_j$, and $L_{\mathrm{size}}$ a natural number. Write `short` = `allocatedShortAxis U basis Lsize` (a predicate on layer-sampler axes; the others are active), $\mathrm{Out}$ = $\Sigma$ `AllocatedCongruenceRankOutput X E short` (a finite type of congruence output coordinates), $\mathrm{Joint}$ = $X \sqcup$ `AllocatedActiveIntegerAxis U basis Lsize`, and $\mathrm{Cont} = \Sigma_j I_j$.
--
--   Let $\mathrm{PIndex}$ and $\Omega$ be finite types and $Z$ a type; let `inactive` be a finite probability law on $\mathrm{PIndex}$, `active i` a finite probability law on $\Omega$ for each $i \in \mathrm{PIndex}$, $\mathrm{gridPoint} : \mathrm{PIndex} \to Z$, and $Y(i, \omega) : \mathrm{Out} \to \mathbb{Z}$. Let $N, q \ge 1$ be natural numbers with ($hq$) $q \mid N$, and `gridVolume` a real number. Let `density` be a real function on pairs (a real vector indexed by $\Sigma_{x \in X}(\mathrm{Unit} \sqcup \emptyset)$, a real vector indexed by the active axes), and `test` $(z, r, y)$ a complex function of $z \in Z$, a residue vector $r : \mathrm{Out} \to \mathbb{Z}/q$ and such a pair $y$. Let $\mathrm{center}, \mathrm{scale} : \mathrm{Joint} \to \mathbb{R}$.
--
--   **Hypotheses.** Assume $\mathrm{gridVolume} \ne 0$; let $\mathrm{cutoff} > 0$ be a natural number; let $D, P, \mathrm{radius}, \delta$ be reals with $D \ge 0$ and $\lvert\mathrm{Out}\rvert + 2 \le P$. Assume the Fourier decay bound: for every $i \in \mathrm{PIndex}$ and every additive character $\chi$ of $(\mathbb{Z}/N)^{\mathrm{Out}}$,
--   $$\bigl\lVert \texttt{finiteImageCharacteristic}(\texttt{active}\ i,\ \omega \mapsto Y(i,\omega) \bmod N,\ \chi)\bigr\rVert \le D \cdot \operatorname{ord}(\chi)^{-P}$$
--   (`finiteImageCharacteristic p f χ` is the $p$-mean of $\chi \circ f$). Let $C, L, K \in \mathbb{R}_{\ge 0}$ with `density` $L$-Lipschitz, nonnegative and bounded by $\lvert\mathrm{density}(y)\rvert \le C$; each `test z r` $K$-Lipschitz and bounded in norm by $1$; $\mathrm{scale}(j) > 0$ for every $j$; $\mathrm{radius} \ge 0$; $0 \le \delta \le 1$; $q \cdot \mathrm{cutoff}/\mathrm{scale}(j) \le \delta$ for every $j$; and $\mathrm{density}(y) = 0$ whenever $\lVert y\rVert > \mathrm{radius}$.
--
--   **Conclusion.** Let $\Lambda$ = `forecastJointOriginalGridMean U basis Lsize hm inactive active gridPoint Y N q hq gridVolume density test center scale` (a complex number defined by OpenAI), and let
--   $$\Lambda' = \sum_{z \in Z} \mathbb{E}_{r : \mathrm{Out} \to \mathbb{Z}/N} \frac{\texttt{rationalInactiveForecast inactive active gridPoint Y N gridVolume}\ z\ r}{\mathrm{gridVolume}} \int \texttt{test}\bigl(z, a \mapsto r(a) \bmod q, y\bigr)\, \mathrm{density}(y)\, dy$$
--   (the sum is a `tsum`, and the integral is against Lebesgue measure with density `density`). Then
--   $$\lVert \Lambda - \Lambda'\rVert \le \Bigl(\mathrm{cutoff}^{\lvert\mathrm{Out}\rvert + 1} \cdot 2(2\,\mathrm{radius} + 2)^{\lvert\mathrm{Joint}\rvert}(L + CK)\delta + \frac{D}{\mathrm{cutoff}}(2\,\mathrm{radius} + 2)^{\lvert\mathrm{Joint}\rvert} L \delta\Bigr)(2\,\mathrm{radius})^{\lvert\mathrm{Cont}\rvert} + \frac{2D}{\mathrm{cutoff}} \int \mathrm{density}(y)\, dy.$$
--
--   Lean: `OAI.Erdos3.VectorPolynomial.forecastJointOriginalGridMean_comparison_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.forecastJointOriginalGridMean_comparison` (in `lean/OAI/Combinatorics/Progressions/Sampling/AllocatedFixedPathRecoveredJointGridComparison.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B218` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Sampling/AllocatedFixedPathRecoveredJointGridComparison.lean (declaration OAI.Erdos3.VectorPolynomial.forecastJointOriginalGridMean_comparison)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B218

section

namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped Classical BigOperators NNReal
variable {X : Type*} [Fintype X]
variable {m : ℕ} {I E : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
variable {n : Fin m → ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (Lsize : ℕ) (hm : 0 < m)
local notation "short" => allocatedShortAxis (I := I) U basis Lsize
local notation "Out" => Sigma (AllocatedCongruenceRankOutput X E short)
local notation "Aux" => (Σ j : Fin m, E j)
local notation "IntAxis" => AllocatedActiveIntegerAxis U basis Lsize
local notation "Joint" => X ⊕ IntAxis
local notation "Cont" => (Σ j : Fin m, I j)
local notation "axis" => forecastCongruenceJointAxisEquiv (X := X) (I := I) (E := E) U basis Lsize hm
local notation "join" => forecastJointCoordinateJoin (X := X) (I := I) U basis Lsize

variable {PIndex Ω Z : Type*} [Fintype PIndex] [Fintype Ω]
variable (inactive : FiniteProbabilityWeights PIndex) (active : PIndex → FiniteProbabilityWeights Ω)
variable (gridPoint : PIndex → Z) (Y : PIndex → Ω → Sigma (AllocatedCongruenceRankOutput X E
  (allocatedShortAxis (I := I) U basis Lsize)) → ℤ)
variable (N q : ℕ) [NeZero N] (hq : q ∣ N) (gridVolume : ℝ)
variable (density : (((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
  ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis Lsize a}, Unit) → ℝ)) → ℝ)
variable (test : Z → (Sigma (AllocatedCongruenceRankOutput X E
  (allocatedShortAxis (I := I) U basis Lsize)) → ZMod q) →
  (((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
  ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis Lsize a}, Unit) → ℝ)) → ℂ)
variable (center scale : X ⊕ AllocatedActiveIntegerAxis U basis Lsize → ℝ)

variable [NeZero q]

theorem forecastJointOriginalGridMean_comparison_s2
    (hV : gridVolume ≠ 0) (cutoff : ℕ) (hcutoff : 0 < cutoff)
    {D P radius δ : ℝ} (hD : 0 ≤ D)
    (hP : ((Fintype.card Out + 2 : ℕ) : ℝ) ≤ P)
    (hdecay : ∀ i (χ : AddChar (Out → ZMod N) ℂ),
      ‖finiteImageCharacteristic (active i) (fun x j => (Y i x j : ZMod N)) χ‖ ≤
        D * (orderOf χ : ℝ) ^ (-P))
    (C L K : ℝ≥0) (hg : LipschitzWith L density) (hg0 : ∀ y, 0 ≤ density y)
    (htest : ∀ z r, LipschitzWith K (test z r))
    (hcap : ∀ y, |density y| ≤ C) (hbound : ∀ z r y, ‖test z r y‖ ≤ 1)
    (hscale : ∀ j, 0 < scale j) (hradius : 0 ≤ radius) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hmesh : ∀ j, ((q * cutoff : ℕ) : ℝ) / scale j ≤ δ)
    (hsupport : ∀ y, radius < ‖y‖ → density y = 0) :
    ‖forecastJointOriginalGridMean U basis Lsize hm inactive active gridPoint Y N q hq
      gridVolume density test center scale -
      (∑' z, 𝔼 r : Out → ZMod N,
        ((rationalInactiveForecast inactive active gridPoint Y N gridVolume z r / gridVolume : ℝ) : ℂ) *
          ∫ y, test z (fun a => ZMod.castHom hq (ZMod q) (r a)) y
            ∂realDensityMeasure volume density)‖ ≤
      ((cutoff : ℝ) ^ (Fintype.card Out + 1) *
        (2 * (2 * radius + 2) ^ Fintype.card Joint * ((L : ℝ) + C * K) * δ) +
        (D / cutoff) * ((2 * radius + 2) ^ Fintype.card Joint * (L : ℝ) * δ)) *
          (2 * radius) ^ Fintype.card Cont +
        (2 * (D / cutoff)) * ∫ y, density y := by
  sorry

end Erdos3.VectorPolynomial

end

end OAI
end
