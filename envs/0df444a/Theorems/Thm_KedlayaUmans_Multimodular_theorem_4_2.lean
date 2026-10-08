-- Prove2me | Theorems.Thm_KedlayaUmans_Multimodular_theorem_4_2
-- name    : KedlayaUmans.Multimodular.theorem_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:47:16.13411+00:00
-- url     : https://prove2.me/theorems/c0267652-c39f-4937-902a-7100b536f193
-- title:
--   Theorem 4.2 — Algorithm MULTIMODULAR returns $f(\alpha_i)$ (correctness)
-- statement:
--   Let $r \ge 1$, $m \ge 1$, $d \ge 2$ and $t \ge 1$ be integers. Let $f \in (\mathbb Z/r\mathbb Z)[X_0,\dots,X_{m-1}]$ have degree at most $d-1$ in each variable, and let $\alpha \in (\mathbb Z/r\mathbb Z)^m$. Then Algorithm MULTIMODULAR with degree parameter $d$ and $t$ rounds returns the value of $f$ at $\alpha$:
--   $$\mathrm{MULTIMODULAR}_d(f, \alpha, r, t) = f(\alpha).$$
--
--   This is the correctness half of Theorem 4.2: multimodular reduction followed by Chinese remaindering computes multivariate multipoint evaluation over $\mathbb Z/r\mathbb Z$ exactly. The algorithm treats the $N$ evaluation points of the paper independently, so the statement for one arbitrary point covers all $N$.
--
--   **Formalization Note** The running-time half of Theorem 4.2 is not formalized. The hypotheses $d \ge 2$ and $m \ge 1$ are implicit in the paper and needed: for $r = 2$, $d = 1$, $f = 1$ the algorithm finds no primes and returns $0$. $r \ge 1$ excludes `ZMod 0 = ℤ`. The value $t = 0$ is excluded.
-- source:
--   Kedlaya, Umans, Fast polynomial factorization and modular composition, Dagstuhl Seminar Proceedings 08381 (version of Aug. 31, 2008), p. 13, Theorem 4.2

import Mathlib
import Definitions.Def_KedlayaUmans_Multimodular_Algorithm

namespace KedlayaUmans.Multimodular

/-- **Theorem 4.2** (correctness half). For `t ≥ 1` rounds, Algorithm MULTIMODULAR returns
`f(α)` for every `f ∈ (ℤ/rℤ)[X₀, …, X_{m-1}]` of degree at most `d - 1` in each variable and every
`α ∈ (ℤ/rℤ)^m`. -/
theorem theorem_4_2 {m r : ℕ} [NeZero r] (d t : ℕ) (ht : 1 ≤ t) (hd : 2 ≤ d) (hm : 1 ≤ m)
    (f : MvPolynomial (Fin m) (ZMod r)) (hf : ∀ i, f.degreeOf i ≤ d - 1)
    (α : Fin m → ZMod r) :
    multimodular d t r f α = MvPolynomial.eval α f := by sorry

end KedlayaUmans.Multimodular
