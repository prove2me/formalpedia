-- Prove2me | Theorems.Thm_OnlinePerceptronIsolation_Binary_lemma_4_1
-- name    : OnlinePerceptronIsolation.Binary.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:57:11.181264+00:00
-- url     : https://prove2.me/theorems/c7717d24-e441-42ab-bf5f-ea4202cb34c5
-- title:
--   Lemma 4.1 — matching a suffix-parallel baseline
-- statement:
--   Let $h:\mathbb N\to\mathbb R$ tend to infinity with eventually $h(n)<n$, and let $a:\mathbb N\to\mathbb N$ satisfy $a(n)\ge1$ and $a(n)/h(n)\to0$. Define $H_n=\sum_{k=a(n)}^{\lfloor h(n)/2\rfloor}1/k$. Then
--   $$H_n=\Theta(\log(h(n)/a(n))),\qquad H_n^{-1}\longrightarrow0.$$
--   For all sufficiently large $n$, every row dimension $m$, every real margin $\kappa$, and every deterministic online algorithm $A$ admit an integer $a(n)\le r\le\lfloor h(n)/2\rfloor<h(n)$, also $r<n$, such that
--   $$\mathbb P_G\bigl(A(G,\kappa)\in S^{h(n)}(G,\kappa),\ A(G,\kappa)\ne A^{(r)}(G,\kappa)\bigr)\le H_n^{-1}.$$
--   The algorithm $A^{(r)}$ is the actual frozen-prefix baseline. The suffix length is chosen before sampling $G$. The common harmonic bound tends to zero independently of the algorithm. This identifies the precise uniform matching statement needed by Theorem 3.6.
--
--   Differences from the source:
--   - encoding: one-based sign cube and coordinates → zero-based Fin indices and exact real-valued signs; reason: a bijection of coordinate labels preserves every signing and Hamming distance
--   - encoding: existence of an integer-valued suffix-length function and a uniform o(1) bound → eventual pointwise existence before the Gaussian sample, the exact H inverse bound, and its limit; reason: choice assembles the selected lengths into a function; the uniform threshold follows from (4.13)-(4.17)
--   - encoding: asymptotic comparisons and harmonic Theta notation → Filter.Tendsto, eventual inequalities, and Asymptotics.IsTheta; reason: finite initial values do not affect asymptotics
--   - generalization: fixed row dimension and margin, with algorithm-uniform error → the eventual suffix-selection threshold is also uniform over row dimensions and margins; reason: the telescoping argument (4.13)-(4.17) depends only on h and a
-- source:
--   Shuangping Li, Gabe Schoenbach, STOC 2027 submission #485 (October 2026), Lemma 4.1, Eqs. (4.1)-(4.3), printed p.12, PDF p.14; proof Eqs. (4.13)-(4.17), printed p.14, PDF p.16; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/485.pdf

import Mathlib
import Definitions.Def_OnlinePerceptronIsolation_Binary_SuffixBaseline
import Definitions.Def_OnlinePerceptronIsolation_Binary_Harmonic
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace OnlinePerceptronIsolation.Binary

/-- Lemma 4.1, printed p.12 / PDF p.14: exact H⁻¹, its Theta growth, its o(1),
and a suffix length chosen before sampling the matrix. -/
theorem lemma_4_1 (h : ℕ → ℝ) (a : ℕ → ℕ)
    (hgrowth : Tendsto h atTop atTop)
    (hsmall : ∀ᶠ n : ℕ in atTop, h n < n)
    (ha : ∀ n, 1 ≤ a n)
    (haratio : Tendsto (fun n => (a n : ℝ) / h n) atTop (𝓝 0)) :
    Asymptotics.IsTheta atTop (fun n => harmonicWindow (a n) (h n))
      (fun n => Real.log (h n / a n)) ∧
    Tendsto (fun n => (harmonicWindow (a n) (h n))⁻¹) atTop (𝓝 0) ∧
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ (m : ℕ) (κ : ℝ) (A : Fin n → (Fin m × Fin n → ℝ) → ℝ),
        ABPOnline.IsOnlineAlg m n A → ∃ r : ℕ,
          a n ≤ r ∧ r ≤ ⌊h n / 2⌋₊ ∧ (r : ℝ) < h n ∧ r < n ∧
            mismatchSuccess A κ (h n) r ≤ (harmonicWindow (a n) (h n))⁻¹ := by sorry

end OnlinePerceptronIsolation.Binary
