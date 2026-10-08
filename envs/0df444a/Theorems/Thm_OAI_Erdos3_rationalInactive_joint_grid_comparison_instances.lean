-- Prove2me | Theorems.Thm_OAI_Erdos3_rationalInactive_joint_grid_comparison_instances
-- name    : OAI.Erdos3.rationalInactive_joint_grid_comparison_instances
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-08T11:06:56.738189+00:00
-- url     : https://prove2.me/theorems/03f90554-456d-431d-9bd0-fc5e87252326
-- title:
--   Grid sums against the rational inactive forecast approximate the continuous integral
-- statement:
--   Let $I,A,\mathrm{Aux},J,V$ be finite types ($\mathrm{Aux}$ and $J$ with decidable equality) and $Z$ any type. Let $\mathrm{inactive}$ be a `FiniteProbabilityWeights I` and $\mathrm{active} : I\to$ `FiniteProbabilityWeights A` (a `FiniteProbabilityWeights X` bundles nonnegative weights on $X$ summing to $1$), $\mathrm{gridPoint} : I\to Z$, and $Y : I\to A\to(\mathrm{Aux}\oplus J)\to\mathbb{Z}$. Let $\mathrm{gridVolume}\ne 0$ be real; let $N\ne 0$ and $q_W\ne 0$ be natural numbers with $q_W\mid N$; let $\mathrm{cutoff}>0$ be a natural number. Let $D,P$ be real numbers with $0\le D$ and $|\mathrm{Aux}\oplus J|+2\le P$, and assume the decay bound: for every $i\in I$ and every additive character $\chi$ of $(\mathbb{Z}/N)^{\mathrm{Aux}\oplus J}$,
--   $$\big|\texttt{finiteImageCharacteristic}\ (\mathrm{active}\ i)\ (Y_i \bmod N)\ \chi\big|\le D\cdot\mathrm{ord}(\chi)^{-P},$$
--   where `finiteImageCharacteristic p f χ` is $\sum_x p.\mathrm{weight}(x)\,\chi(f(x))$ and $\mathrm{ord}(\chi)$ is the order of $\chi$. Let $g : \mathbb{R}^V\times\mathbb{R}^J\to\mathbb{R}$ and $\varphi : Z\to(\mathbb{Z}/q_W)^{\mathrm{Aux}\oplus J}\to\mathbb{R}^V\times\mathbb{R}^J\to\mathbb{C}$, and let $C,L,K\ge 0$ be reals in $\mathbb{R}_{\ge0}$ such that $g$ is $L$-Lipschitz, $g\ge 0$, each $\varphi(z,b,\cdot)$ is $K$-Lipschitz, $|g|\le C$ and $|\varphi|\le 1$ everywhere (the metrics are Mathlib's sup metrics on products). Let $\mathrm{center},T : J\to\mathbb{R}$ with $T_j>0$ for all $j$; let $R,\delta$ be real with $0\le R$ and $0\le\delta\le 1$, with $q_W\cdot\mathrm{cutoff}/T_j\le\delta$ for every $j$, and with $g(x)=0$ whenever $\|x\|>R$. Write $F(z,b)$ for `rationalInactiveForecast inactive active gridPoint Y N gridVolume z b` (the real number $\mathrm{gridVolume}$ times OpenAI's fiber mean, under $\mathrm{inactive}$ over the fiber $\mathrm{gridPoint}^{-1}(z)$, of OpenAI's `rationalOutputDensity` of $\mathrm{active}\ i$ and $Y_i$ at $b\in(\mathbb{Z}/N)^{\mathrm{Aux}\oplus J}$), write $\rho$ for the coordinatewise reduction $(\mathbb{Z}/N)^{\mathrm{Aux}\oplus J}\to(\mathbb{Z}/q_W)^{\mathrm{Aux}\oplus J}$ (`zmodPiReduction`), and for $k\in\mathbb{Z}^J$ write $u_k=\big((k_j-\mathrm{center}_j)/T_j\big)_{j\in J}$. Then the norm of the difference between
--   $$\mathbb{E}_{\mathrm{aux}\in(\mathbb{Z}/N)^{\mathrm{Aux}}}\int_{\mathbb{R}^V}\frac{\sum_{z}\sum_{k\in\mathbb{Z}^J} g(c,u_k)\,\frac{F(z,(\mathrm{aux},k\bmod N))}{\mathrm{gridVolume}}\,\varphi\big(z,(\rho(\mathrm{aux}),k\bmod q_W),(c,u_k)\big)}{\prod_{j}T_j}\,dc$$
--   and
--   $$\sum_{z}\ \mathbb{E}_{b\in(\mathbb{Z}/N)^{\mathrm{Aux}\oplus J}}\frac{F(z,b)}{\mathrm{gridVolume}}\int_{\mathbb{R}^V\times\mathbb{R}^J} g(y)\,\varphi(z,\rho(b),y)\,dy$$
--   (the sums over $z\in Z$ and $k$ are Mathlib's unconditional sums `tsum`, the integrals are against Lebesgue measure, and the expectations are uniform averages) is at most
--   $$\Big(\mathrm{cutoff}^{|\mathrm{Aux}\oplus J|+1}\cdot 2(2R+2)^{|J|}(L+CK)\,\delta+\frac{D}{\mathrm{cutoff}}(2R+2)^{|J|}L\,\delta\Big)(2R)^{|V|}+\frac{2D}{\mathrm{cutoff}}\int_{\mathbb{R}^V\times\mathbb{R}^J} g(y)\,dy.$$
--
--   Lean: `OAI.Erdos3.rationalInactive_joint_grid_comparison_instances` in `lean/OAI/Combinatorics/Progressions/Estimates/RationalInactiveJointComparisonInstances.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B010` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/RationalInactiveJointComparisonInstances.lean#L161

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B010

namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators Classical NNReal

variable {I A Z Aux J V : Type*} [Fintype I] [Fintype A] [Fintype Aux] [Fintype J] [Fintype V]

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators Classical NNReal
variable {I A Z Aux J V : Type*} [Fintype I] [Fintype A] [Fintype Aux] [Fintype J] [Fintype V]
variable [instAux : DecidableEq Aux] [instJ : DecidableEq J]

theorem rationalInactive_joint_grid_comparison_instances
    (inactive : FiniteProbabilityWeights I) (active : I → FiniteProbabilityWeights A)
    (gridPoint : I → Z) (Y : I → A → (Aux ⊕ J) → ℤ)
    {gridVolume : ℝ} (hV : gridVolume ≠ 0)
    {N : ℕ} [NeZero N] (qW : ℕ) [NeZero qW] (hW : qW ∣ N)
    (cutoff : ℕ) (hcutoff : 0 < cutoff)
    {D P : ℝ} (hD : 0 ≤ D) (hP : ((Fintype.card (Aux ⊕ J) + 2 : ℕ) : ℝ) ≤ P)
    (hdecay : ∀ i (χ : AddChar ((Aux ⊕ J) → ZMod N) ℂ),
      ‖finiteImageCharacteristic (active i) (fun x j => (Y i x j : ZMod N)) χ‖ ≤
        D * (orderOf χ : ℝ) ^ (-P))
    (g : ((V → ℝ) × (J → ℝ)) → ℝ)
    (φ : Z → ((Aux ⊕ J) → ZMod qW) → ((V → ℝ) × (J → ℝ)) → ℂ)
    (C L K : ℝ≥0) (hg : LipschitzWith L g) (hg0 : ∀ x, 0 ≤ g x)
    (hφ : ∀ z b, LipschitzWith K (φ z b))
    (hcap : ∀ x, |g x| ≤ C) (hbound : ∀ z b x, ‖φ z b x‖ ≤ 1)
    (center T : J → ℝ) (hT : ∀ j, 0 < T j)
    {R δ : ℝ} (hR : 0 ≤ R) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hmesh : ∀ j, ((qW * cutoff : ℕ) : ℝ) / T j ≤ δ)
    (hsupport : ∀ x, R < ‖x‖ → g x = 0) :
    ‖(𝔼 aux : Aux → ZMod N, ∫ c : V → ℝ,
      (∑' z, ∑' k : J → ℤ,
        (g (c, fun j => ((k j : ℝ) - center j) / T j) : ℂ) *
        ((rationalInactiveForecast inactive active gridPoint Y N gridVolume z
          (Sum.elim aux (fun j => (k j : ZMod N))) / gridVolume : ℝ) : ℂ) *
        φ z (Sum.elim (zmodPiReduction hW aux) (fun j => (k j : ZMod qW)))
          (c, fun j => ((k j : ℝ) - center j) / T j)) /
        ((∏ j, T j : ℝ) : ℂ)) -
      (∑' z, 𝔼 b : (Aux ⊕ J) → ZMod N,
        ((rationalInactiveForecast inactive active gridPoint Y N gridVolume z b /
          gridVolume : ℝ) : ℂ) *
        ∫ y, (g y : ℂ) * φ z (zmodPiReduction hW b) y
          ∂((volume : Measure (V → ℝ)).prod (volume : Measure (J → ℝ))))‖ ≤
      ((cutoff : ℝ) ^ (Fintype.card (Aux ⊕ J) + 1) *
        (2 * (2 * R + 2) ^ Fintype.card J * ((L : ℝ) + C * K) * δ) +
        (D / cutoff) * ((2 * R + 2) ^ Fintype.card J * (L : ℝ) * δ)) *
          (2 * R) ^ Fintype.card V +
        (2 * (D / cutoff)) * ∫ y, g y
          ∂((volume : Measure (V → ℝ)).prod (volume : Measure (J → ℝ))) := by
  sorry

end Erdos3
end
end OAI
