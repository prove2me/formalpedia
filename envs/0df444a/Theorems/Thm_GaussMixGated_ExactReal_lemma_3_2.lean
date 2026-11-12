-- Prove2me | Theorems.Thm_GaussMixGated_ExactReal_lemma_3_2
-- name    : GaussMixGated.ExactReal.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T15:25:53.764961+00:00
-- url     : https://prove2.me/theorems/274fbc66-2ab2-4b1b-9578-e05cbcfa2310
-- title:
--   Lemma 3.2 — A finite gate
-- statement:
--   Let $F:\mathbb R^n\to\mathbb R^r$ be a polynomial map of degree at most $q$, $v>0$ and $T>0$. Take eight independent sketches (16) and accept exactly when every squared norm is at most $T$. For a gate input $A\sim N(u,vI_n)$ independent of the sketches let $\alpha(u)$ be the acceptance probability, and $K_q=3^{8q}e^{12q}$. Then
--
--   1. if $F\ne0$, $\alpha(u)\le\min\{1,K_qT^2/M(u)^2\}$;
--   2. $\alpha(u)M(u)\le\sqrt{K_q}\,T$;
--   3. $1-\alpha(u)\le8\cdot2^qM(u)/T$;
--   4. if $F=0$ (equivalently $M\equiv0$), $\alpha(u)=1$.
--
--   The gate thus suppresses atoms with large conditional second moment while retaining atoms with small moment, which is what localizes the accepted moments.
--
--   Differences from the source:
--   - encoding: α(u) ≤ min{1, K_q T²/M(u)²} with the convention 'when M = 0 the gate accepts with probability one' → the min bound for F ≠ 0, and α = 1 for F = 0; reason: Lean's x/0 = 0 would turn the printed bound into α ≤ 0 at M = 0; M > 0 exactly when F ≠ 0, and the zero sketch is accepted since T > 0
--   - encoding: v^{h/2} → (√v)^h; reason: equal for v > 0
-- source:
--   Zheng, Xie, He, Learning Finite Gaussian Location Mixtures via Gated Moments and Posterior Covers, STOC 2027 submission #36 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/36.pdf, PDF p. 10 (printed p. 8), §3.2, Lemma 3.2, (17)–(18); sketch (16) on PDF p. 9

import Mathlib
import Definitions.Def_GaussMixGated_ExactReal_Jet

namespace GaussMixGated.ExactReal

/-- Lemma 3.2 (A finite gate) (Zheng–Xie–He, STOC 2027 #36, PDF p. 10): the gate accepting
exactly when all eight independent sketches (16) have squared norm at most `T > 0` has, for a
gate input `A ∼ N(u, v I_n)`, acceptance probability `α(u)` with
`α(u) ≤ min{1, K_q T²/M(u)²}` (for `F ≠ 0`), `α(u) M(u) ≤ √K_q · T`,
`1 − α(u) ≤ 8 · 2^q M(u)/T`, and `α = 1` when `F = 0` (`M = 0`). -/
theorem lemma_3_2 {n r : ℕ} (F : PolyMap n r) (q : ℕ) (hF : F.DegLE q) (v T : ℝ) (hv : 0 < v)
    (hT : 0 < T) (u : Fin n → ℝ) :
    (F ≠ 0 → gateAcceptance F q v T u ≤ min 1 (Kconst q * T ^ 2 / momentM F v u ^ 2)) ∧
    gateAcceptance F q v T u * momentM F v u ≤ Real.sqrt (Kconst q) * T ∧
    1 - gateAcceptance F q v T u ≤ 8 * 2 ^ q * momentM F v u / T ∧
    (F = 0 → gateAcceptance F q v T u = 1) := by sorry

end GaussMixGated.ExactReal
