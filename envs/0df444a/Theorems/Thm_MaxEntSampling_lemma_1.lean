-- Prove2me | Theorems.Thm_MaxEntSampling_lemma_1
-- name    : MaxEntSampling.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:58:35.599591+00:00
-- url     : https://prove2.me/theorems/5343a2ff-d8a8-48e9-94f1-7f5540ac74f6
-- title:
--   Lemma 1 — $\max_{X\succeq0}\{\log\det^s(X)-\operatorname{tr}(X\Lambda)\}=-\log\det_s(\Lambda)-s$
-- statement:
--   Let $\Lambda\in\mathbb R^{d\times d}$ be symmetric positive definite and $s\in[d]$. Then
--
--   $$
--   \max_{X\succeq0}\Bigl\{\log{\det}^s(X)-\operatorname{tr}(X\Lambda)\Bigr\} = -\log{\det}_s(\Lambda)-s, \tag{4}
--   $$
--
--   and the maximum is attained.
--
--   This is the convex conjugate of $-\log\det^s$ that turns the Lagrangian of MESP (3) into the dual LD (5).
--
--   **Formalization Note** $\log\det^s(X)$ is extended-real valued with $\log0=-\infty$, so singular $X$ contribute $-\infty$; the right-hand side is real because $\det_s(\Lambda)>0$. The maximum is stated as a greatest element.
--
--   Differences from the source:
--   - encoding: log det^s(X) with log 0 = −∞ → EReal via ENNReal.log ∘ ENNReal.ofReal; reason: the paper's convention (Appendix A.4); same values
--   - reading: max_{X⪰0} → IsGreatest (the value is an upper bound and is attained); reason: Appendix A.2 constructs the maximizer X* = P Diag(1/β1,…,1/βs,0,…,0) Pᵀ
-- source:
--   Li, Xie, Best Principal Submatrix Selection for the Maximum Entropy Sampling Problem, arXiv:2001.08537v3, Lemma 1, eq. (4), p.7 (PDF p.7); proof Appendix A.2, pp.41–42

import Mathlib
import Definitions.Def_MaxEntSampling_detTop
import Definitions.Def_MaxEntSampling_detBot

open Matrix

namespace MaxEntSampling

/-- **Lemma 1: the conjugate identity `max_{X⪰0} {log det^s(X) − tr(XΛ)} = −log det_s(Λ) − s` (4).**
Li, Xie, *Best Principal Submatrix Selection for the Maximum Entropy Sampling Problem*,
arXiv:2001.08537v3, Lemma 1, eq. (4), p.7 (PDF p.7); proof in Appendix A.2, pp.41–42.

For every symmetric positive definite `Λ ∈ ℝ^{d×d}` and every `s ∈ [d]`, the value
`log det^s(X) − tr(XΛ)` is at most `−log det_s(Λ) − s` for every `X ⪰ 0`, and some `X ⪰ 0`
attains it.

**Formalization Note.** `log det^s(X)` lies in `EReal` with `log 0 = −∞`
(`ENNReal.log ∘ ENNReal.ofReal`), so a singular `X` contributes `−∞`, not a junk `0`.
`det_s(Λ) > 0` for `Λ ≻ 0`, so the right-hand side is a real number. "max" is stated as
`IsGreatest` (the maximum is attained, by the maximizer constructed in A.2). `X ⪰ 0` is
`Matrix.PosSemidef` (symmetric and positive semidefinite). -/
theorem lemma_1 {d : ℕ} (s : ℕ) (hs1 : 1 ≤ s) (hsd : s ≤ d) (Λ : Matrix (Fin d) (Fin d) ℝ)
    (hΛ : Λ.PosDef) :
    IsGreatest {z : EReal | ∃ X : Matrix (Fin d) (Fin d) ℝ, X.PosSemidef ∧
        z = ENNReal.log (ENNReal.ofReal (detTop s X)) - (((X * Λ).trace : ℝ) : EReal)}
      ((-Real.log (detBot s Λ) - s : ℝ) : EReal) := by sorry

end MaxEntSampling
