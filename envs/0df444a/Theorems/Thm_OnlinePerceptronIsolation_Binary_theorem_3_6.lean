-- Prove2me | Theorems.Thm_OnlinePerceptronIsolation_Binary_theorem_3_6
-- name    : OnlinePerceptronIsolation.Binary.theorem_3_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:55:38.887879+00:00
-- url     : https://prove2.me/theorems/e159af4c-ffff-4a77-b9b1-2ccf4d4a37d1
-- title:
--   Theorem 3.6 — deterministic bound uniform over algorithms
-- statement:
--   Fix a density $\alpha>0$, a margin $\kappa\in\mathbb R$, and a real function $h$ such that $h(n)/(\log n)^4\to+\infty$ and eventually $h(n)<n$. For $m=\lfloor\alpha n\rfloor$ and every deterministic measurable online algorithm $A$, let success mean that its output belongs to the full set $S^{h(n)}(G,\kappa)$ of isolated solutions. Then
--   $$\forall\varepsilon>0\ \exists N\ \forall n\ge N\ \forall A\in\mathrm{ONLINE}_{\mathrm{det}}(m,n),\quad \mathbb P_G(A(G,\kappa)\in S^{h(n)}(G,\kappa))<\varepsilon.$$
--   Here $G$ has independent standard Gaussian entries. The threshold $N$ depends on $\alpha,\kappa,h,\varepsilon$ and is independent of $A$, including dimension-dependent choices. This is the deterministic hardness target used for the randomized goal.
--
--   Differences from the source:
--   - encoding: one-based sign cube and coordinates → zero-based Fin indices and exact real-valued signs; reason: a bijection of coordinate labels preserves every signing and Hamming distance
--   - encoding: the nonnegative success probability is o(1) → for every positive epsilon there is one threshold for all size-n algorithms; reason: the source explicitly provides algorithm-uniformity in Theorem 3.6 and its extension in A.6
--   - encoding: h(n)<n in the asymptotic regime → h(n)<n eventually; reason: changing finitely many radii changes no asymptotic assertion
-- source:
--   Shuangping Li, Gabe Schoenbach, STOC 2027 submission #485 (October 2026), Theorem 3.6, Eq. (3.13), printed p.11, PDF p.13; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/485.pdf

import Mathlib
import Definitions.Def_OnlinePerceptronIsolation_Binary_Isolation
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace OnlinePerceptronIsolation.Binary

/-- Theorem 3.6, printed p.11 / PDF p.13, including uniformity over algorithms. -/
theorem theorem_3_6 (α κ : ℝ) (hα : 0 < α) (h : ℕ → ℝ)
    (hgrowth : Tendsto (fun n => h n / (Real.log n) ^ 4) atTop atTop)
    (hsublinear : ∀ᶠ n : ℕ in atTop, h n < n) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ A : Fin n → (Fin ⌊α * n⌋₊ × Fin n → ℝ) → ℝ,
        ABPOnline.IsOnlineAlg ⌊α * n⌋₊ n A → detSuccess A κ (h n) < ε := by sorry

end OnlinePerceptronIsolation.Binary
