-- Prove2me | Theorems.Thm_OnlinePerceptronIsolation_Binary_Supplement_lemma_4_1_K
-- name    : OnlinePerceptronIsolation.Binary.Supplement.lemma_4_1_K
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:10:59.76688+00:00
-- url     : https://prove2.me/theorems/516f2d80-4028-4957-8836-e020295e0418
-- title:
--   Lemma 4.1 (ONLINE_K version, §4.3) — matching a suffix baseline
-- statement:
--   Let $h:\mathbb N\to\mathbb R$ tend to $+\infty$ with $h(n)<n$ eventually. Let $a:\mathbb N\to\mathbb N$ satisfy $a(n)\ge1$ for every $n$ and $a(n)/h(n)\to0$. Define the exact harmonic sum
--   $$H_n=\sum_{k=a(n)}^{\lfloor h(n)/2\rfloor}\frac1k.$$
--   Then
--   $$H_n=\Theta\!\left(\log\frac{h(n)}{a(n)}\right),\qquad H_n^{-1}\longrightarrow0.$$
--   There is a threshold $N$, uniform over the row dimension $m$, every set $K\subseteq\mathbb R$ and every deterministic online algorithm $A$, such that for $n\ge N$ some integer $r$, selected before sampling $G$, satisfies
--   $$a(n)\le r\le\lfloor h(n)/2\rfloor,\qquad r<h(n),\quad r<n,\qquad\mathbb P_G\{A(G)\in S^{h(n)}(G,K),\ A(G)\ne A^{(r)}(G)\}\le H_n^{-1}.$$
--   The baseline $A^{(r)}$ is the computed suffix-parallel baseline. This supplies the matching step of Theorem 3.2. No well-separation hypothesis is imposed on $K$.
--
--   Differences from the source:
--   - encoding: one-based sign cube and real coordinates → zero-based Fin indices and exact real-valued signs; reason: coordinate relabelling preserves all signings, scores and Hamming distances
--   - encoding: integer suffix function and o(1) mismatch bound with exact H inverse → eventual uniform existence of a pre-sampling suffix r, the IsTheta assertion, and convergence of H inverse; reason: these are the three conclusions of Lemma 4.1 and its algorithm-independent averaging proof, applied verbatim in §4.3
--   - generalization: a fixed row dimension m and a fixed set K, with an algorithm-independent bound → the eventual suffix-selection threshold N is uniform over every row dimension m and every set K; reason: the harmonic averaging argument (4.13)-(4.17) depends only on h and a, so each fixed (m, K) instance of the source is a specialization
-- source:
--   Shuangping Li, Gabe Schoenbach, STOC 2027 submission #485 (October 2026), Lemma 4.1 (ONLINE_K version, §4.3), printed p. 15, PDF p. 17; original Lemma 4.1 printed pp. 12–14, PDF pp. 14–16; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/485.pdf

import Mathlib
import Definitions.Def_OnlinePerceptronIsolation_Binary_Supplement_MismatchSuccessK
import Definitions.Def_OnlinePerceptronIsolation_Binary_Harmonic
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace OnlinePerceptronIsolation.Binary.Supplement

/-- Lemma 4.1 applied verbatim to ONLINE_K, as stated in section 4.3, printed p.15.
All three conclusions and the exact harmonic bound are retained, for every set K. -/
theorem lemma_4_1_K (h : ℕ → ℝ) (a : ℕ → ℕ)
    (hgrowth : Tendsto h atTop atTop)
    (hsmall : ∀ᶠ n : ℕ in atTop, h n < n)
    (ha : ∀ n, 1 ≤ a n)
    (haratio : Tendsto (fun n => (a n : ℝ) / h n) atTop (𝓝 0)) :
    Asymptotics.IsTheta atTop (fun n => harmonicWindow (a n) (h n))
      (fun n => Real.log (h n / a n)) ∧
    Tendsto (fun n => (harmonicWindow (a n) (h n))⁻¹) atTop (𝓝 0) ∧
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ (m : ℕ) (K : Set ℝ) (A : Fin n → (Fin m × Fin n → ℝ) → ℝ),
        ABPOnline.IsOnlineAlg m n A → ∃ r : ℕ,
          a n ≤ r ∧ r ≤ ⌊h n / 2⌋₊ ∧ (r : ℝ) < h n ∧ r < n ∧
            mismatchSuccessK A K (h n) r ≤ (harmonicWindow (a n) (h n))⁻¹ := by sorry

end OnlinePerceptronIsolation.Binary.Supplement
