-- Prove2me | Theorems.Thm_FriendlyShadow_Gaussian_lemma_39
-- name    : FriendlyShadow.Gaussian.lemma_39
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T20:17:00.082726+00:00
-- url     : https://prove2.me/theorems/0f47982d-bd2e-400e-bbff-51c2edc75de8
-- title:
--   Lemma 39, p. 29 — chord combination bound: E[‖C(q)‖₁ | θ, t, S, Ē] ≥ e⁻²/(dL(1 + R_{n,d}))
-- statement:
--   Let $d\ge3$ and write the hyperplane $\mathbb R^{d-1}$ as $U\times\mathbb R\bar\omega$ with $U=\bar\omega^\perp\cong\mathbb R^{d-2}$. Let $\bar\mu_1,\dots,\bar\mu_d$ be positive $L$-log-Lipschitz functions on $\mathbb R^{d-1}$, $L>0$. Let $S=(s_1,\dots,s_d)\in U^d$ be an allowed shape: $s_1=0$, $\operatorname{rank}(s_2,\dots,s_d)=d-2$ and $\|s_i-s_j\|\le2+2R$ for all $i,j$, with $R\ge0$ and $d/3\le LR$ (the conclusion of Lemma 21 for the cutoff radius $R$). Let $z$ be a kernel combination of $S$ and $\bar p\in U$. As in Lemma 38, $q=\bar p-x$ has on $\operatorname{conv}(S)$ the density proportional to
--   $$\hat\mu(q)=\int_{\mathbb R^d}\Big|\sum_{i=1}^d z_ih_i\Big|\prod_{i=1}^d\bar\mu_i(\bar p-q+s_i+h_i\bar\omega)\,dh .$$
--   Then
--   $$\mathbb E\big[\|C(q)\|_1\mid q\in\operatorname{conv}(S)\big]\ \ge\ \frac{e^{-2}}{dL(1+R)},$$
--   stated multiplied out as $\frac{e^{-2}}{dL(1+R)}\int_{\operatorname{conv}(S)}\hat\mu\le\int_{\operatorname{conv}(S)}\|C(q)\|_1\,\hat\mu(q)\,dq$.
--
--   Together with Lemma 41 this gives the lower bound (18) on the expected edge length.
--
--   **Formalization Note** The page conditions on $(\theta,t,S,\bar E)$. Here the conditioning is replaced by the explicit density of $q$ obtained by marginalising Lemma 37's density over the heights; the event $\bar E$ is $q\in\operatorname{conv}(S)$. The factor $|\sum_iz_ih_i|$ is kept: the printed proof drops it, but its argument applies unchanged with the factor present. The page's "by Lemma 21" enters as the hypothesis $d/3\le LR$. The printed last step claims $\alpha\ge1-1/d$, which is too weak for $e^{-2}$; the inequality $d/3\le LR$ gives $1-\alpha\le 3/(2d^2)$, which suffices. $\mathbb R^{d-1}$ carries its Euclidean norm, written in coordinates $(u,h)$ as $\sqrt{\|u-u'\|^2+(h-h')^2}$. Integrals are lower Lebesgue integrals in $[0,\infty]$, over $\operatorname{conv}(S)$ with the Lebesgue measure of $U$.
-- source:
--   Dadush & Huiberts, arXiv:1711.05667v4, Lemma 39, p. 29 (proof p. 30); densities of Lemmas 37–38, pp. 28–29; Lemma 21, p. 21

import Mathlib
import Definitions.Def_FriendlyShadow_Gaussian_Shape

open MeasureTheory
open scoped RealInnerProductSpace

namespace FriendlyShadow.Gaussian

/-- Lemma 39 (Chord combination bound, p. 29), on the explicit density of Lemmas 37–38.
The hyperplane `ℝ^{d−1}` is written as `U × ℝω̄` with `U = ω̄⊥ = ℝ^{d−2}`, and
`mubar i u h = μ̄ᵢ(u + hω̄)` are positive `L`-log-Lipschitz functions. Let `s` be an allowed shape
(`s₁ = 0`, `rank(s₂, …, s_d) = d − 2`, `diam(S) ≤ 2 + 2R`), `z` a kernel combination, and assume
`d/3 ≤ L·R` (Lemma 21). Given `p̄ ∈ U`, `q = p̄ − x` has on `conv(S)` the density proportional to
`∫ |Σ zᵢhᵢ| Π μ̄ᵢ(p̄ − q + sᵢ + hᵢω̄) dh`; then `E[‖C(q)‖₁ | q ∈ conv(S)] ≥ e⁻²/(dL(1 + R))`,
written cross-multiplied with the unnormalised density. -/
theorem lemma_39 {d : ℕ} [NeZero d] (hd : 3 ≤ d)
    (s : Fin d → EuclideanSpace ℝ (Fin (d - 2))) (hs0 : s 0 = 0)
    (hrank : Module.finrank ℝ (Submodule.span ℝ (Set.range s)) = d - 2)
    (L R : ℝ) (hL : 0 < L) (hR : 0 ≤ R) (hdiam : ∀ i j, ‖s i - s j‖ ≤ 2 + 2 * R)
    (hLR : (d : ℝ) / 3 ≤ L * R) (z : Fin d → ℝ) (hz : IsKernelComb s z)
    (mubar : Fin d → EuclideanSpace ℝ (Fin (d - 2)) → ℝ → ℝ)
    (hpos : ∀ i u h, 0 < mubar i u h)
    (hlip : ∀ i u u' h h', mubar i u h ≤
      Real.exp (L * Real.sqrt (‖u - u'‖ ^ 2 + (h - h') ^ 2)) * mubar i u' h')
    (p : EuclideanSpace ℝ (Fin (d - 2))) :
    ENNReal.ofReal (Real.exp (-2) / (d * L * (1 + R))) *
        ∫⁻ q in convexHull ℝ (Set.range s), heightMarginal mubar s z (p - q) ≤
      ∫⁻ q in convexHull ℝ (Set.range s),
        ENNReal.ofReal (chordLen s q) * heightMarginal mubar s z (p - q) := by sorry

end FriendlyShadow.Gaussian
