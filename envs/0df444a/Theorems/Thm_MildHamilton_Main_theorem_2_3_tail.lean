-- Prove2me | Theorems.Thm_MildHamilton_Main_theorem_2_3_tail
-- name    : MildHamilton.Main.theorem_2_3_tail
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:46:23.800174+00:00
-- url     : https://prove2.me/theorems/f74cf527-3ed7-4d7a-aefc-eeadefbc5169
-- title:
--   Theorem 2.3, 'in particular' clause only, p. 4 — deviation form of matrix Bernstein (the displayed inequality is the companion MatrixTail.Bernstein.theorem6_1) (corrected: 0 ≤ R)
-- statement:
--   Let $X_1,\dots,X_n$ be independent random self-adjoint $d\times d$ matrices, $d\ge1$, with $R\ge0$, $\mathbb E X_k=0$ and $\lambda_{\max}(X_k)\le R$ almost surely for every $k$, and let $\sigma^2=\big\|\sum_k\mathbb E(X_k^2)\big\|$. Then for every $t>0$, with probability at least $1-d\,e^{-t}$,
--
--   $$\lambda_{\max}\Big(\sum_k X_k\Big)\le\sqrt{2\sigma^2t}+\frac23Rt.$$
--
--   This is the form of matrix Bernstein used to sample columns in Lemma 2.4. It covers only the 'in particular' clause of Theorem 2.3; the displayed tail inequality of that theorem is the published open item `MatrixTail.Bernstein.theorem6_1`.
--
--   **Formalization Note** The event is written with strict inequality as the failure event, whose probability is at most $d\,e^{-t}$. Matrices are complex, which contains the real symmetric case by casting entries.
--
--   Differences from the source:
--   - reading: r and s, undefined in the clause → the dimension d and the number n of summands; reason: the use in Lemma 2.4 (r × r matrices, s columns) fixes this reading
--   - correction: no sign condition on R, a finite sequence → the hypothesis 0 ≤ R; reason: for a nonempty sequence 0 ≤ R follows from E X_k = 0 and λ_max(X_k) ≤ R, so no such instance is lost; the only excluded instance is the empty sequence with R < 0, where the printed bound fails (d = 1, λ_max(0) = 0 exceeds (2/3)Rt, and 1 > e^{−t})
--   - encoding: E X_k and E(X_k²) exist, X_k are random matrices → measurable X_k with entrywise integrable X_k and X_k², and d ≥ 1 by NeZero; reason: without integrability the Bochner integral returns 0; the dimension of a matrix with an eigenvalue is at least 1
-- source:
--   Alp Muyesser, STOC 2027 submission #233 (October 2026), Theorem 2.3 ('in particular' clause), p. 4

import Mathlib
import Definitions.Def_MatrixTail_Gaussian_Model
import Definitions.Def_MatrixTail_Master_Model

open MeasureTheory ProbabilityTheory

namespace MildHamilton.Main

/-- Theorem 2.3, 'in particular' clause (Muyesser, STOC 2027 submission #233, p. 4): matrix Bernstein in
deviation form. The displayed inequality of Theorem 2.3 is `MatrixTail.Bernstein.theorem6_1`. The printed
`r` is the dimension `d` and the printed `s` is the number `n` of summands.
Corrected by `0 ≤ R`: for an empty sequence, `d = 1`, `R = -1`, and `t = 1`, the printed
threshold is `-2/3` while the empty sum has largest eigenvalue `0`; its failure probability
is `1 > exp (-1)`. For a nonempty sequence the mean-zero and upper-bound assumptions imply `0 ≤ R`. -/
theorem theorem_2_3_tail {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n d : ℕ} [NeZero d] (X : Fin n → Ω → Matrix (Fin d) (Fin d) ℂ)
    (hX_meas : ∀ k, Measurable (X k)) (hX_herm : ∀ k ω, (X k ω).IsHermitian)
    (hX_indep : iIndepFun X P)
    (hX_int : ∀ k, MatrixTail.Master.MatIntegrable P (X k))
    (hX2_int : ∀ k, MatrixTail.Master.MatIntegrable P (fun ω => X k ω ^ 2))
    (hX_mean : ∀ k, MatrixTail.Master.mean P (X k) = 0)
    (R : ℝ) (hR : 0 ≤ R) (hX_max : ∀ k, ∀ᵐ ω ∂P, MatrixTail.Master.lambdaMax (X k ω) ≤ R)
    (σsq : ℝ)
    (hσ : σsq = MatrixTail.Gaussian.specNorm (∑ k, MatrixTail.Master.mean P (fun ω => X k ω ^ 2)))
    (t : ℝ) (ht : 0 < t) :
    P.real {ω | Real.sqrt (2 * σsq * t) + 2 / 3 * R * t < MatrixTail.Master.lambdaMax (∑ k, X k ω)} ≤
      (d : ℝ) * Real.exp (-t) := by sorry

end MildHamilton.Main
