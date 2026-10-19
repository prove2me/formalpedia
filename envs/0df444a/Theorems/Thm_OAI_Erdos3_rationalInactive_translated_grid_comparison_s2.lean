-- Prove2me | Theorems.Thm_OAI_Erdos3_rationalInactive_translated_grid_comparison_s2
-- name    : OAI.Erdos3.rationalInactive_translated_grid_comparison_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-17T10:42:17.612019+00:00
-- url     : https://prove2.me/theorems/4c232f4f-0abd-4ba9-b93c-163175a09168
-- title:
--   Comparison of a translated lattice sum of rational inactive forecasts with its residue-averaged integral
-- statement:
--   Let $I$, $A$, $\mathrm{Aux}$, $J$ be finite types and $Z$ a type. Let `inactive` be a finite probability law on $I$, `active i` a finite probability law on $A$ for each $i \in I$, $\mathrm{gridPoint} : I \to Z$ and $Y(i, x) : \mathrm{Aux} \sqcup J \to \mathbb{Z}$. Let `gridVolume` be a nonzero real, $N \ge 1$ and $q_W \ge 1$ natural numbers with $q_W \mid N$, $\mathrm{aux} : \mathrm{Aux} \to \mathbb{Z}/N$, and $\mathrm{cutoff} > 0$ a natural number. Let $D, P$ be reals with $D \ge 0$ and $\lvert \mathrm{Aux} \sqcup J\rvert + 2 \le P$, and assume the Fourier decay bound: for every $i$ and every additive character $\chi$ of $(\mathbb{Z}/N)^{\mathrm{Aux} \sqcup J}$,
--   $$\bigl\lVert \texttt{finiteImageCharacteristic}(\texttt{active}\ i,\ x \mapsto Y(i, x) \bmod N,\ \chi)\bigr\rVert \le D \cdot \operatorname{ord}(\chi)^{-P}$$
--   (`finiteImageCharacteristic p f χ` is the $p$-mean of $\chi \circ f$).
--
--   Let $g : \mathbb{R}^J \to \mathbb{R}$ and $\varphi(z, b, x) \in \mathbb{C}$ for $z \in Z$, $b \in (\mathbb{Z}/q_W)^J$, $x \in \mathbb{R}^J$. Let $C, L, K \in \mathbb{R}_{\ge 0}$ with $g$ $L$-Lipschitz, $g \ge 0$, $\lvert g\rvert \le C$, each $\varphi(z, b, \cdot)$ $K$-Lipschitz, and $\lVert\varphi\rVert \le 1$. Let $\mathrm{center}, T : J \to \mathbb{R}$ with $T > 0$, and reals $R \ge 0$ and $0 \le \delta \le 1$ with $q_W \cdot \mathrm{cutoff}/T(j) \le \delta$ for every $j$ and $g(x) = 0$ whenever $\lVert x\rVert > R$.
--
--   Write $F(z, \beta)$ = `rationalInactiveForecast inactive active gridPoint Y N gridVolume z β` / gridVolume for $\beta : \mathrm{Aux} \sqcup J \to \mathbb{Z}/N$ (OpenAI: $F(z, \beta)$ is the `inactive`-mean over the fiber $\mathrm{gridPoint} = z$ of the rational output density of $Y(i, \cdot)$ at $\beta$), and for $k \in \mathbb{Z}^J$ write $x_k = ((k_j - \mathrm{center}(j))/T(j))_j$. Then
--   $$\Bigl\lVert \frac{1}{\prod_j T(j)} \sum_{z} \sum_{k \in \mathbb{Z}^J} g(x_k)\, F\bigl(z, \mathrm{aux} \sqcup (k \bmod N)\bigr)\, \varphi(z, k \bmod q_W, x_k) - \sum_{z} \mathbb{E}_{b \in (\mathbb{Z}/N)^J} F(z, \mathrm{aux} \sqcup b) \int g(x)\, \varphi(z, b \bmod q_W, x)\, dx \Bigr\rVert$$
--   is at most
--   $$\mathrm{cutoff}^{\lvert\mathrm{Aux} \sqcup J\rvert + 1} \cdot 2(2R + 2)^{\lvert J\rvert}(L + CK)\delta + \frac{D}{\mathrm{cutoff}}\Bigl(2\int g + (2R+2)^{\lvert J\rvert} L\delta\Bigr).$$
--   (The sums over $z \in Z$ and $k \in \mathbb{Z}^J$ are `tsum`s; $b \bmod q_W$ is `zmodPiReduction`; integrals are against Lebesgue measure.)
--
--   Lean: `OAI.Erdos3.rationalInactive_translated_grid_comparison_s2`, which states OpenAI's `OAI.Erdos3.rationalInactive_translated_grid_comparison` (in `lean/OAI/Combinatorics/Progressions/Sampling/RationalInactiveGridIntegralComparison.lean`); the definitions it uses are in the definitions bundles `OAIE3v2B085`, `OAIE3v2B105` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Sampling/RationalInactiveGridIntegralComparison.lean (declaration OAI.Erdos3.rationalInactive_translated_grid_comparison)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B085
import Definitions.Def_OAIE3v2B105

section

namespace OAI

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators Classical NNReal
variable {I A Z Aux J : Type*} [Fintype I] [Fintype A] [Fintype Aux] [Fintype J]

theorem rationalInactive_translated_grid_comparison_s2
    (inactive : FiniteProbabilityWeights I) (active : I → FiniteProbabilityWeights A)
    (gridPoint : I → Z) (Y : I → A → (Aux ⊕ J) → ℤ)
    {gridVolume : ℝ} (hV : gridVolume ≠ 0)
    {N : ℕ} [NeZero N] (qW : ℕ) [NeZero qW] (hW : qW ∣ N)
    (aux : Aux → ZMod N) (cutoff : ℕ) (hcutoff : 0 < cutoff)
    {D P : ℝ} (hD : 0 ≤ D) (hP : ((Fintype.card (Aux ⊕ J) + 2 : ℕ) : ℝ) ≤ P)
    (hdecay : ∀ i (χ : AddChar ((Aux ⊕ J) → ZMod N) ℂ),
      ‖finiteImageCharacteristic (active i) (fun x j => (Y i x j : ZMod N)) χ‖ ≤
        D * (orderOf χ : ℝ) ^ (-P))
    (g : (J → ℝ) → ℝ) (φ : Z → (J → ZMod qW) → (J → ℝ) → ℂ)
    (C L K : ℝ≥0) (hg : LipschitzWith L g) (hg0 : ∀ x, 0 ≤ g x)
    (hφ : ∀ z b, LipschitzWith K (φ z b))
    (hcap : ∀ x, |g x| ≤ C) (hbound : ∀ z b x, ‖φ z b x‖ ≤ 1)
    (center T : J → ℝ) (hT : ∀ j, 0 < T j)
    {R δ : ℝ} (hR : 0 ≤ R) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hmesh : ∀ j, ((qW * cutoff : ℕ) : ℝ) / T j ≤ δ)
    (hsupport : ∀ x, R < ‖x‖ → g x = 0) :
    ‖(∑' z, ∑' k : J → ℤ,
        (g (fun j => ((k j : ℝ) - center j) / T j) : ℂ) *
        ((rationalInactiveForecast inactive active gridPoint Y N gridVolume z
          (Sum.elim aux (fun j => (k j : ZMod N))) / gridVolume : ℝ) : ℂ) *
        φ z (fun j => (k j : ZMod qW)) (fun j => ((k j : ℝ) - center j) / T j)) /
        ((∏ j, T j : ℝ) : ℂ) -
      (∑' z, 𝔼 b : J → ZMod N,
        ((rationalInactiveForecast inactive active gridPoint Y N gridVolume z
          (Sum.elim aux b) / gridVolume : ℝ) : ℂ) *
        ∫ x, (g x : ℂ) * φ z (zmodPiReduction hW b) x)‖ ≤
      (cutoff : ℝ) ^ (Fintype.card (Aux ⊕ J) + 1) *
        (2 * (2 * R + 2) ^ Fintype.card J * ((L : ℝ) + C * K) * δ) +
      (D / cutoff) * (2 * (∫ x, g x) +
        (2 * R + 2) ^ Fintype.card J * (L : ℝ) * δ) := by
  sorry

end Erdos3

end

end OAI
end
