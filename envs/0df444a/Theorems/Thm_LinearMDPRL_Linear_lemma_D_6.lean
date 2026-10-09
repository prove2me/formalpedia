-- Prove2me | Theorems.Thm_LinearMDPRL_Linear_lemma_D_6
-- name    : LinearMDPRL.Linear.lemma_D_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T01:47:35.264968+00:00
-- url     : https://prove2.me/theorems/9e025d1b-9681-4506-b0d6-f56e38c4792a
-- title:
--   Lemma D.6, p. 28 — log N_ε(𝒱) ≤ d log(1 + 4L/ε) + d² log[1 + 8d^{1/2}B²/(λε²)]
-- statement:
--   Let $\mathcal V$ be the class of functions $\mathcal S\to\mathbb R$ of the form
--   $$
--   V(\cdot)=\min\Big\{\max_a\Big[w^\top\phi(\cdot,a)+\beta\sqrt{\phi(\cdot,a)^\top\Lambda^{-1}\phi(\cdot,a)}\Big],\ H\Big\}
--   $$
--   with $\|w\|\le L$, $\beta\in[0,B]$ and $\lambda_{\min}(\Lambda)\ge\lambda$, where $L,B\ge0$ and $\lambda>0$. Assume $\|\phi(x,a)\|\le1$ for all $(x,a)$. Then for every $\varepsilon>0$ there is a finite family $\mathcal N$ of functions $\mathcal S\to\mathbb R$ such that every $V\in\mathcal V$ is within $\varepsilon$ of some member of $\mathcal N$ in the distance $\mathrm{dist}(V,V')=\sup_x|V(x)-V'(x)|$, and
--   $$
--   \log|\mathcal N|\le d\log(1+4L/\varepsilon)+d^2\log\big[1+8d^{1/2}B^2/(\lambda\varepsilon^2)\big].
--   $$
--   Equivalently, the $\varepsilon$-covering number $\mathcal N_\varepsilon$ of $\mathcal V$ satisfies this bound.
--
--   The bound is polynomial in $d$ and logarithmic in the scale, independent of $|\mathcal S|$ and $|\mathcal A|$; it is the complexity term in the uniform concentration of Lemma D.4.
--
--   **Formalization Note.** The covering number is expressed by exhibiting a cover of the stated size, without a covering-number API. The centers of the cover are arbitrary real functions on $\mathcal S$ (an external cover), which is what the proof constructs: its centers are parametrized by a net of weights and a net of matrices in a Frobenius ball. $\Lambda$ is taken symmetric, as "minimum eigenvalue" presupposes.
-- source:
--   Jin, Yang, Wang, Jordan, arXiv:1907.05388v2, Lemma D.6, p. 28

import Mathlib
import Definitions.Def_LinearMDPRL_Linear_ProofObjects

namespace LinearMDPRL.Linear

/-- **Lemma D.6** (arXiv:1907.05388v2, p. 28). Let `𝒱` be the class of functions
`V(·) = min{ max_a w^⊤ φ(·, a) + β √(φ(·, a)^⊤ Λ^{-1} φ(·, a)), H }` with `‖w‖ ≤ L`,
`β ∈ [0, B]` and `λ_min(Λ) ≥ λ`, and assume `‖φ(x, a)‖ ≤ 1` for all `(x, a)`. Then for every
`ε > 0` the class `𝒱` has an `ε`-cover `N` in the distance `dist(V, V') = sup_x |V(x) − V'(x)|`
with `log |N| ≤ d log(1 + 4L/ε) + d² log[1 + 8 d^{1/2} B² / (λ ε²)]`. -/
theorem lemma_D_6 {S A : Type*} [Fintype A] [Nonempty A] {d : ℕ}
    (φ : S → A → EuclideanSpace ℝ (Fin d)) (hφ : ∀ x a, ‖φ x a‖ ≤ 1)
    (H L B lam ε : ℝ) (hL : 0 ≤ L) (hB : 0 ≤ B) (hlam : 0 < lam) (hε : 0 < ε) :
    ∃ N : Finset (S → ℝ),
      (∀ V ∈ valueClass φ H L B lam, ∃ V' ∈ N, ∀ x, |V x - V' x| ≤ ε) ∧
      Real.log N.card ≤ d * Real.log (1 + 4 * L / ε) +
        (d : ℝ) ^ 2 * Real.log (1 + 8 * Real.sqrt d * B ^ 2 / (lam * ε ^ 2)) := by sorry

end LinearMDPRL.Linear
