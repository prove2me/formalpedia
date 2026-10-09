-- Prove2me | Theorems.Thm_OAI_Erdos3_CellRefinement_normalized_bilinear_refinement_step
-- name    : OAI.Erdos3.CellRefinement.normalized_bilinear_refinement_step
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T00:28:58.998703+00:00
-- url     : https://prove2.me/theorems/13d68a47-98d1-40a2-bdda-41eb90e2a039
-- title:
--   Normalized refinement step: a cell bilinear bound on admissible children passes to the parent
-- statement:
--   Let $N$ be a positive natural number and $\varepsilon$ a real number; write $\delta = $ `flatComparisonDelta ε` $= \varepsilon/(4(2+\varepsilon))$ and $\gamma = $ `localMomentGain δ` (a real number defined by OpenAI). A `CyclicBohr.Set N` $B$ is OpenAI's structure of a finite set of frequencies in $\mathbb{Z}/N$ and a radius $\ge 0$; its carrier is $\{x \in \mathbb{Z}/N : |1 - e(rx/N)| \le \text{radius for all frequencies } r\}$, its rank is the number of frequencies, and $B.\mathrm{ndilate}\ t$ is the same set with radius multiplied by $t \ge 0$; `IsRankRegular` is OpenAI's regularity predicate on such sets, and `Peeling.admissibleBohrShape B₀ scale extra minimumWidth C` means that $C$ is rank-regular, its carrier lies in that of $B_0.\mathrm{ndilate}\ \mathrm{scale}$, $C.\mathrm{rank} \le B_0.\mathrm{rank} + \mathrm{extra}$ and $\mathrm{minimumWidth} \le C.\mathrm{radius}$. Write `bilinearIntegral X Y a f g` for the average over $x \in X$, $y \in Y$ of $f(x)g(y)a(x+y)$, and `CellBilinearBound C a T` for the predicate: for every origin $o$ and all $f, g : \mathbb{Z}/N \to [0,1]$ vanishing off $C$, `bilinearIntegral C C (r ↦ a(o+r)) f g` $\le T(\mathbb{E}_C f \cdot \mathbb{E}_C g)^{1/4}$.
--
--   Let $B_0, L, S$ be `CyclicBohr.Set N` with $B_0$ and $L$ rank-regular, $0 < S.\mathrm{radius} \le 1$, $S$ rank-regular, $1 \le S.\mathrm{rank}$, $S$ and $L$ having the same frequencies, and $S.\mathrm{radius} \le L.\mathrm{radius}$. Let $\kappa, \mathrm{scale} \in \mathbb{R}_{\ge 0}$, $\mathrm{extra} \in \mathbb{N}$ and $\mathrm{minimumWidth}, p, D, R, P, H, W, Q, E \in \mathbb{R}$. Assume $0 < \varepsilon$, $1 \le p$, $0 \le D$, $0 \le R$, $0 \le H$; the carrier of $S$ lies in that of $L.\mathrm{ndilate}\ \kappa$; $\kappa + \kappa \le 1/(100 \cdot 2\max(L.\mathrm{rank},1))$; $\mathrm{scale} \le 1/(100\cdot 2\max(B_0.\mathrm{rank},1))$; the carrier of $S$ lies in that of $B_0.\mathrm{ndilate}\ \mathrm{scale}$; $S.\mathrm{rank} + $ `unbalancedRankExtra γ p H` $\le B_0.\mathrm{rank} + \mathrm{extra}$; $\mathrm{minimumWidth} \le S.\mathrm{radius}\cdot\exp(-$`unbalancedReturnWidthLoss` $(S.\mathrm{rank}, \gamma, p, H, Q, E))$ (both explicit functions of OpenAI); and `Peeling.admissibleBohrShape B₀ scale extra minimumWidth L`. Let $A, B : \mathbb{Z}/N \to \mathbb{R}$ with $0 \le A, B \le e^{p}$ pointwise. Let $M, K, c_0, \mathrm{cutoff} \in \mathbb{R}$ with $0 < c_0$, $0 < K$, $0 < \mathrm{cutoff}$, $2 \le \tfrac14 K^{3/4}$, $(c_0K)^{1/4} \le 1/2$, $0 < M \le e^{p}$, $1 \le M c_0\,\mathrm{cutoff}$ and $W\,\mathrm{cutoff}^{3/4} \le e^{-Dp}$. Assume the carrier of $S$ lies in that of $L.\mathrm{ndilate}$ (`controlledLocalMomentScale` $(L.\mathrm{rank}, M, \delta)$), a nonnegative real defined by OpenAI; $M^2\cdot 400\max(L.\mathrm{rank},1)(\kappa+\kappa) \le \gamma/32$; $e^{-R} \le S.\mathrm{radius}$; $2S.\mathrm{rank} + p + (D+2)p + R + 1612 \le P$ and $(D+2)p + 2 + S.\mathrm{rank}(R+10) \le P$; `CyclicNiltestUpperComparison 1 N P (exp(-P)) A B` (at universe $0$: for every rational filtered nilmanifold of degree at most $1$ and every unit-interval-valued niltest $T$ of complexity at most $P$ on it, the average over $\mathbb{Z}/N$ of $(A(x) - B(x))\,\mathrm{Re}\,T(x)$ is at most $e^{-P}$); $0 \le W \le e^{Q}$, $0 \le Q$, $0 \le E$, and $|A(r) - (1+\varepsilon)B(r)| \le W$ for all $r$. Let $\mathrm{matchingError} \in \mathbb{R}$ be such that for every origin $o \in \mathbb{Z}/N$ and all $f, g : \mathbb{Z}/N \to [0,1]$, with $a_o(r) = A(o+r) - (1+\varepsilon)B(o+r)$,
--   $|\texttt{bilinearIntegral}\ B_0.\mathrm{carrier}\ B_0.\mathrm{carrier}\ a_o\ f\ g - \texttt{parentTruncatedIntegral}\ B_0.\mathrm{carrier}\ B_0.\mathrm{carrier}\ L.\mathrm{carrier}\ S.\mathrm{carrier}\ a_o\ f\ g| \le \mathrm{matchingError}$, where `parentTruncatedIntegral` is a real-valued average of matched integrals defined by OpenAI. Let $m$ be a positive natural number with $(2 + (D+1) + \log 3)\,p \le 2m\log 2$ such that, for every natural $m'$ with $m \le m' \le$ `localMomentExponentFactor δ` $\cdot m$ (a natural number defined by OpenAI), $2m' \le Hp$ and $(1+\gamma/4)^{2m'} \le (\gamma/64)/2\cdot(1+\gamma/2)^{2m'}$. Finally let $T \ge 0$ be such that `CellBilinearBound C.carrier (fun r => A r - (1+ε) B r) T` holds for every $C$ with `Peeling.admissibleBohrShape B₀ scale extra minimumWidth C`. Then, with $\rho = 1 - \gamma/(128(1+\sqrt{K/c_0})^2)$, `CellBilinearBound B₀.carrier (fun r => A r - (1+ε) B r) T'` holds with
--   $$T' = T\,\tfrac{1+\rho}{2} + e^{-Dp} + \frac{e^{-E} + \mathrm{matchingError}}{\mathrm{cutoff}^2} + \frac{2W\cdot 400\max(B_0.\mathrm{rank},1)\,\mathrm{scale}}{K\,\mathrm{cutoff}^3}.$$
--
--   Lean: `OAI.Erdos3.CellRefinement.normalized_bilinear_refinement_step` in `lean/OAI/Combinatorics/Progressions/Estimates/RefinementEnlargement.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B034` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/RefinementEnlargement.lean#L935

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B034

namespace OAI

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3.CellRefinement

open LocalConvolution
open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N]

end Erdos3.CellRefinement

end

section

namespace Erdos3.CellRefinement

open LocalConvolution
open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N] {epsilon : ℝ}

local notation "δ" => flatComparisonDelta epsilon
local notation "γ" => localMomentGain δ

end Erdos3.CellRefinement

end

section

namespace Erdos3.CellRefinement

open LocalConvolution
open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N] {epsilon : ℝ}

local notation "δ" => flatComparisonDelta epsilon
local notation "γ" => localMomentGain δ

end Erdos3.CellRefinement

end

section

namespace Erdos3.CellRefinement

open LocalConvolution
open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N] {epsilon : ℝ}

local notation "δ" => flatComparisonDelta epsilon
local notation "γ" => localMomentGain δ

end Erdos3.CellRefinement

end

section

namespace Erdos3.CellRefinement

open LocalConvolution
open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N] {epsilon : ℝ}

local notation "δ" => flatComparisonDelta epsilon
local notation "γ" => localMomentGain δ

end Erdos3.CellRefinement

end

section

namespace Erdos3.CellRefinement

open LocalConvolution
open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N] {epsilon : ℝ}

local notation "δ" => flatComparisonDelta epsilon
local notation "γ" => localMomentGain δ

end Erdos3.CellRefinement

end

section

namespace Erdos3.CellRefinement

open LocalConvolution
open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N] {epsilon : ℝ}

local notation "δ" => flatComparisonDelta epsilon
local notation "γ" => localMomentGain δ

end Erdos3.CellRefinement

end

section

namespace Erdos3.CellRefinement

open LocalConvolution
open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N] {epsilon : ℝ}

local notation "δ" => flatComparisonDelta epsilon
local notation "γ" => localMomentGain δ

theorem normalized_bilinear_refinement_step
    (B₀ L S : CyclicBohr.Set N) (hB₀ : B₀.IsRankRegular) (hL : L.IsRankRegular)
    (hSpos : 0 < S.radius) (hSwidth : S.radius ≤ 1)
    (hSreg : S.IsRankRegular) (hSrank : 1 ≤ S.rank)
    (hfreq : S.frequencies = L.frequencies) (hlocalWidth : S.radius ≤ L.radius)
    {kappa scale : ℝ≥0} {extra : ℕ} {minimumWidth p D R P H W Q E : ℝ}
    (hepsilon : 0 < epsilon) (hp : 1 ≤ p) (hD : 0 ≤ D) (hR : 0 ≤ R) (hH : 0 ≤ H)
    (hSL : S.carrier ⊆ (L.ndilate kappa).carrier)
    (hkappa : kappa + kappa ≤ 1 / (100 * (2 * max L.rank 1 : ℕ) : ℝ≥0))
    (hscale : scale ≤ 1 / (100 * (2 * max B₀.rank 1 : ℕ) : ℝ≥0))
    (hSB : S.carrier ⊆ (B₀.ndilate scale).carrier)
    (hrank : S.rank + unbalancedRankExtra γ p H ≤ B₀.rank + extra)
    (hwidth : minimumWidth ≤ S.radius * Real.exp (-unbalancedReturnWidthLoss S.rank γ p H Q E))
    (hLshape : Peeling.admissibleBohrShape B₀ scale extra minimumWidth L)
    (A B : ZMod N → ℝ)
    (hA : ∀ r, 0 ≤ A r ∧ A r ≤ Real.exp p)
    (hB : ∀ r, 0 ≤ B r ∧ B r ≤ Real.exp p)
    {M K c₀ cutoff : ℝ} (hc₀ : 0 < c₀) (hK : 0 < K) (hcutoff : 0 < cutoff)
    (hKfactor : 2 ≤ (1 / 4 : ℝ) * K ^ (3 / 4 : ℝ))
    (hfactor : (c₀ * K) ^ (1 / 4 : ℝ) ≤ 1 / 2)
    (hM : 0 < M) (hMcap : M ≤ Real.exp p)
    (hMcutoff : 1 ≤ M * (c₀ * cutoff))
    (htiny : W * cutoff ^ (3 / 4 : ℝ) ≤ Real.exp (-(D * p)))
    (hSLmoment : S.carrier ⊆ (L.ndilate (controlledLocalMomentScale L.rank M δ)).carrier)
    (herror : M ^ 2 * (400 * (max L.rank 1 : ℕ) * ((kappa + kappa : ℝ≥0) : ℝ)) ≤ γ / 32)
    (hSlog : Real.exp (-R) ≤ S.radius)
    (hcomplexity : 2 * (S.rank : ℝ) + p + (D + 2) * p + R + 1612 ≤ P)
    (hprecision : (D + 2) * p + 2 + (S.rank : ℝ) * (R + 10) ≤ P)
    (hcompare : CyclicNiltestUpperComparison.{0} 1 N P (Real.exp (-P)) A B)
    (hW : 0 ≤ W) (hWcap : W ≤ Real.exp Q) (hQ : 0 ≤ Q) (hE : 0 ≤ E)
    (ha : ∀ r, |A r - (1 + epsilon) * B r| ≤ W)
    {matchingError : ℝ}
    (hmatching : ∀ origin : ZMod N, ∀ f g : ZMod N → ℝ,
      (∀ r, 0 ≤ f r ∧ f r ≤ 1) → (∀ r, 0 ≤ g r ∧ g r ≤ 1) →
      |bilinearIntegral B₀.carrier B₀.carrier
          (fun r => A (origin + r) - (1 + epsilon) * B (origin + r)) f g -
        parentTruncatedIntegral B₀.carrier B₀.carrier L.carrier S.carrier
          (fun r => A (origin + r) - (1 + epsilon) * B (origin + r)) f g| ≤ matchingError)
    (m : ℕ) (hm : 0 < m)
    (horder : (1 + 1 + (D + 1) + Real.log 3) * p ≤ ((2 * m : ℕ) : ℝ) * Real.log 2)
    (horders : ∀ m' : ℕ, m ≤ m' → m' ≤ localMomentExponentFactor δ * m →
      ((2 * m' : ℕ) : ℝ) ≤ H * p ∧
      (1 + γ / 4) ^ (2 * m') ≤ (γ / 64) / 2 * (1 + γ / 2) ^ (2 * m'))
    {T : ℝ} (hT : 0 ≤ T)
    (hchildren : ∀ C, Peeling.admissibleBohrShape B₀ scale extra minimumWidth C →
      CellBilinearBound C.carrier (fun r => A r - (1 + epsilon) * B r) T) :
    let rho := 1 - γ / (128 * (1 + Real.sqrt (K / c₀)) ^ 2)
    CellBilinearBound B₀.carrier (fun r => A r - (1 + epsilon) * B r)
      (T * ((1 + rho) / 2) + Real.exp (-(D * p)) +
        (Real.exp (-E) + matchingError) / cutoff ^ 2 +
        2 * (W * (400 * (max B₀.rank 1 : ℕ) * (scale : ℝ))) / (K * cutoff ^ 3)) := by
  sorry

end Erdos3.CellRefinement
end
end OAI
