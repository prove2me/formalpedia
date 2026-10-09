-- Prove2me | Theorems.Thm_OAI_Erdos3_CellRefinement_capped_parent_bound_of_children
-- name    : OAI.Erdos3.CellRefinement.capped_parent_bound_of_children
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T00:23:35.099184+00:00
-- url     : https://prove2.me/theorems/07e07cf8-5bab-4984-a6e7-694a97a72e3f
-- title:
--   Capped parent step: a bilinear bound on admissible children bounds the parent integral
-- statement:
--   Let $N$ be a positive natural number and $\varepsilon$ a real number; write $\delta = $ `flatComparisonDelta ε` $= \varepsilon/(4(2+\varepsilon))$ and $\gamma = $ `localMomentGain δ` (a real number defined by OpenAI). A `CyclicBohr.Set N` $B$ is OpenAI's structure of a finite set of frequencies in $\mathbb{Z}/N$ and a radius $\ge 0$; its carrier is $\{x \in \mathbb{Z}/N : |1 - e(rx/N)| \le \text{radius for all frequencies } r\}$, its rank is the number of frequencies, and $B.\mathrm{ndilate}\ t$ is the same set with radius multiplied by $t \ge 0$; `IsRankRegular` is OpenAI's regularity predicate on such sets, and `Peeling.admissibleBohrShape B₀ scale extra minimumWidth C` means that $C$ is rank-regular, its carrier lies in that of $B_0.\mathrm{ndilate}\ \mathrm{scale}$, $C.\mathrm{rank} \le B_0.\mathrm{rank} + \mathrm{extra}$ and $\mathrm{minimumWidth} \le C.\mathrm{radius}$. Write `cellAverage C f z` for the average of $f(z+c)$ over $c \in C$, and `bilinearIntegral X Y a f g` for the average over $x \in X$, $y \in Y$ of $f(x)g(y)a(x+y)$.
--
--   Let $B_0, L, S$ be `CyclicBohr.Set N` with $L$ rank-regular, $0 < S.\mathrm{radius} \le 1$, $S$ rank-regular, $1 \le S.\mathrm{rank}$, $S$ and $L$ having the same frequencies, and $S.\mathrm{radius} \le L.\mathrm{radius}$. Let $\kappa, \mathrm{scale} \in \mathbb{R}_{\ge 0}$, $\mathrm{extra} \in \mathbb{N}$ and $\mathrm{minimumWidth}, p, D, R, P, H, W, Q, E \in \mathbb{R}$. Assume $0 < \varepsilon$, $1 \le p$, $0 \le D$, $0 \le R$, $0 \le H$; the carrier of $S$ lies in that of $L.\mathrm{ndilate}\ \kappa$; $\kappa + \kappa \le 1/(100 \cdot 2\max(L.\mathrm{rank},1))$; the carrier of $S$ lies in that of $B_0.\mathrm{ndilate}\ \mathrm{scale}$; $S.\mathrm{rank} + $ `unbalancedRankExtra γ p H` $\le B_0.\mathrm{rank} + \mathrm{extra}$; $\mathrm{minimumWidth} \le S.\mathrm{radius}\cdot\exp(-$`unbalancedReturnWidthLoss` $(S.\mathrm{rank}, \gamma, p, H, Q, E))$ (both explicit functions of OpenAI); and `Peeling.admissibleBohrShape B₀ scale extra minimumWidth L`. Let $A, B, F, G : \mathbb{Z}/N \to \mathbb{R}$ and $\mathrm{origin} \in \mathbb{Z}/N$, with $0 \le A, B \le e^{p}$ and $0 \le F, G \le 1$ pointwise, and $F$, $G$ vanishing off the carrier of $B_0$. Let $U, V, M, K, c_0 \in \mathbb{R}$ with $0 < U$, $0 < V$, $0 < c_0$, $0 \le K$; assume the averages of $F$ and of $G$ over the carrier of $B_0$ equal $U$ and $V$; $(c_0 K)^{1/4} \le 1/2$; for every `CyclicBohr.Set N` $C$ with `Peeling.admissibleBohrShape B₀ scale extra minimumWidth C` and every $z$, `cellAverage` $(C.\mathrm{carrier}, F, z) \le KU$ and `cellAverage` $(C.\mathrm{carrier}, G, z) \le KV$; $0 < M \le e^{p}$, $1 \le M c_0 U$, $1 \le M c_0 V$; the carrier of $S$ lies in that of $L.\mathrm{ndilate}$ (`controlledLocalMomentScale` $(L.\mathrm{rank}, M, \delta)$), a nonnegative real defined by OpenAI; $M^2 \cdot 400\max(L.\mathrm{rank},1)(\kappa+\kappa) \le \gamma/32$; $e^{-R} \le S.\mathrm{radius}$; $2S.\mathrm{rank} + p + (D+2)p + R + 1612 \le P$ and $(D+2)p + 2 + S.\mathrm{rank}(R+10) \le P$; `CyclicNiltestUpperComparison 1 N P (exp(-P)) A B` (at universe $0$: for every rational filtered nilmanifold of degree at most $1$ and every unit-interval-valued niltest $T$ of complexity at most $P$ on it, the average over $\mathbb{Z}/N$ of $(A(x) - B(x))\,\mathrm{Re}\,T(x)$ is at most $e^{-P}$); $0 \le W \le e^{Q}$, $0 \le Q$, $0 \le E$, and $|A(r) - (1+\varepsilon)B(r)| \le W$ for all $r$. Put $a(r) = A(\mathrm{origin}+r) - (1+\varepsilon)B(\mathrm{origin}+r)$, and let $\mathrm{matchingError} \in \mathbb{R}$ with
--   $|\texttt{bilinearIntegral}\ B_0.\mathrm{carrier}\ B_0.\mathrm{carrier}\ a\ F\ G - \texttt{parentTruncatedIntegral}\ B_0.\mathrm{carrier}\ B_0.\mathrm{carrier}\ L.\mathrm{carrier}\ S.\mathrm{carrier}\ a\ F\ G| \le \mathrm{matchingError}$, where `parentTruncatedIntegral` is a real-valued average of matched integrals defined by OpenAI. Let $m$ be a positive natural number with $(2 + (D+1) + \log 3)\,p \le 2m\log 2$ such that, for every natural $m'$ with $m \le m' \le$ `localMomentExponentFactor δ` $\cdot m$ (a natural number defined by OpenAI), $2m' \le Hp$ and $(1+\gamma/4)^{2m'} \le (\gamma/64)/2\cdot(1+\gamma/2)^{2m'}$. Finally let $T \ge 0$ be such that every $C$ with `Peeling.admissibleBohrShape B₀ scale extra minimumWidth C` satisfies `CellBilinearBound C.carrier (fun r => A r - (1+ε) B r) T`: for every origin $o$ and all $f, g : \mathbb{Z}/N \to [0,1]$ vanishing off $C.\mathrm{carrier}$, `bilinearIntegral` $(C.\mathrm{carrier}, C.\mathrm{carrier}, r \mapsto A(o+r) - (1+\varepsilon)B(o+r), f, g) \le T\bigl(\mathbb{E}_{C} f \cdot \mathbb{E}_{C} g\bigr)^{1/4}$. Then, with $\rho = 1 - \gamma/(128(1 + \sqrt{K/c_0})^2)$,
--   $$\texttt{bilinearIntegral}\ B_0.\mathrm{carrier}\ B_0.\mathrm{carrier}\ a\ F\ G \le \Bigl(T\,\tfrac{1+\rho}{2} + e^{-Dp}\Bigr)(UV)^{1/4} + e^{-E} + \mathrm{matchingError}.$$
--
--   Lean: `OAI.Erdos3.CellRefinement.capped_parent_bound_of_children` in `lean/OAI/Combinatorics/Progressions/Estimates/RefinementEnlargement.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B034` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/RefinementEnlargement.lean#L729

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

theorem capped_parent_bound_of_children
    (B₀ L S : CyclicBohr.Set N) (hL : L.IsRankRegular)
    (hSpos : 0 < S.radius) (hSwidth : S.radius ≤ 1)
    (hSreg : S.IsRankRegular) (hSrank : 1 ≤ S.rank)
    (hfreq : S.frequencies = L.frequencies) (hlocalWidth : S.radius ≤ L.radius)
    {kappa scale : ℝ≥0} {extra : ℕ} {minimumWidth p D R P H W Q E : ℝ}
    (hepsilon : 0 < epsilon) (hp : 1 ≤ p) (hD : 0 ≤ D) (hR : 0 ≤ R) (hH : 0 ≤ H)
    (hSL : S.carrier ⊆ (L.ndilate kappa).carrier)
    (hkappa : kappa + kappa ≤ 1 / (100 * (2 * max L.rank 1 : ℕ) : ℝ≥0))
    (hSB : S.carrier ⊆ (B₀.ndilate scale).carrier)
    (hrank : S.rank + unbalancedRankExtra γ p H ≤ B₀.rank + extra)
    (hwidth : minimumWidth ≤ S.radius * Real.exp (-unbalancedReturnWidthLoss S.rank γ p H Q E))
    (hLshape : Peeling.admissibleBohrShape B₀ scale extra minimumWidth L)
    (A B F G : ZMod N → ℝ) (origin : ZMod N)
    (hA : ∀ r, 0 ≤ A r ∧ A r ≤ Real.exp p)
    (hB : ∀ r, 0 ≤ B r ∧ B r ≤ Real.exp p)
    (hF : ∀ r, 0 ≤ F r ∧ F r ≤ 1) (hG : ∀ r, 0 ≤ G r ∧ G r ≤ 1)
    (hFsupport : ∀ r, r ∉ B₀.carrier → F r = 0)
    (hGsupport : ∀ r, r ∉ B₀.carrier → G r = 0)
    {U V M K c₀ : ℝ} (hU : 0 < U) (hV : 0 < V) (hc₀ : 0 < c₀) (hK : 0 ≤ K)
    (hmeanF : (𝔼 r ∈ B₀.carrier, F r) = U) (hmeanG : (𝔼 r ∈ B₀.carrier, G r) = V)
    (hfactor : (c₀ * K) ^ (1 / 4 : ℝ) ≤ 1 / 2)
    (hparentF : ∀ C, Peeling.admissibleBohrShape B₀ scale extra minimumWidth C →
      ∀ z, cellAverage C.carrier F z ≤ K * U)
    (hparentG : ∀ C, Peeling.admissibleBohrShape B₀ scale extra minimumWidth C →
      ∀ z, cellAverage C.carrier G z ≤ K * V)
    (hM : 0 < M) (hMcap : M ≤ Real.exp p)
    (hMU : 1 ≤ M * (c₀ * U)) (hMV : 1 ≤ M * (c₀ * V))
    (hSLmoment : S.carrier ⊆ (L.ndilate (controlledLocalMomentScale L.rank M δ)).carrier)
    (herror : M ^ 2 * (400 * (max L.rank 1 : ℕ) * ((kappa + kappa : ℝ≥0) : ℝ)) ≤ γ / 32)
    (hSlog : Real.exp (-R) ≤ S.radius)
    (hcomplexity : 2 * (S.rank : ℝ) + p + (D + 2) * p + R + 1612 ≤ P)
    (hprecision : (D + 2) * p + 2 + (S.rank : ℝ) * (R + 10) ≤ P)
    (hcompare : CyclicNiltestUpperComparison.{0} 1 N P (Real.exp (-P)) A B)
    (hW : 0 ≤ W) (hWcap : W ≤ Real.exp Q) (hQ : 0 ≤ Q) (hE : 0 ≤ E)
    (ha : ∀ r, |A r - (1 + epsilon) * B r| ≤ W)
    {matchingError : ℝ}
    (hmatching : |bilinearIntegral B₀.carrier B₀.carrier (fun r => A (origin + r) - (1 + epsilon) * B (origin + r)) F G -
      parentTruncatedIntegral B₀.carrier B₀.carrier L.carrier S.carrier
        (fun r => A (origin + r) - (1 + epsilon) * B (origin + r)) F G| ≤ matchingError)
    (m : ℕ) (hm : 0 < m)
    (horder : (1 + 1 + (D + 1) + Real.log 3) * p ≤ ((2 * m : ℕ) : ℝ) * Real.log 2)
    (horders : ∀ m' : ℕ, m ≤ m' → m' ≤ localMomentExponentFactor δ * m →
      ((2 * m' : ℕ) : ℝ) ≤ H * p ∧
      (1 + γ / 4) ^ (2 * m') ≤ (γ / 64) / 2 * (1 + γ / 2) ^ (2 * m'))
    {T : ℝ} (hT : 0 ≤ T)
    (hchildren : ∀ C, Peeling.admissibleBohrShape B₀ scale extra minimumWidth C →
      CellBilinearBound C.carrier (fun r => A r - (1 + epsilon) * B r) T) :
    let rho := 1 - γ / (128 * (1 + Real.sqrt (K / c₀)) ^ 2)
    bilinearIntegral B₀.carrier B₀.carrier
        (fun r => A (origin + r) - (1 + epsilon) * B (origin + r)) F G ≤
      (T * ((1 + rho) / 2) + Real.exp (-(D * p))) * (U * V) ^ (1 / 4 : ℝ) +
        Real.exp (-E) + matchingError := by
  sorry

end Erdos3.CellRefinement
end
end OAI
