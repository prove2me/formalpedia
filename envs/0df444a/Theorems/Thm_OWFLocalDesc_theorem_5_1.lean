-- Prove2me | Theorems.Thm_OWFLocalDesc_theorem_5_1
-- name    : OWFLocalDesc.theorem_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:50:41.532436+00:00
-- url     : https://prove2.me/theorems/c38a4a44-c3c8-45da-9416-0cf8a8dd80e4
-- title:
--   Theorem 5.1 (Robust easiness without one-way functions)
-- statement:
--   Assume one-way functions do not exist. Fix a decoder $U$, a polynomial sample-size schedule $m(n)\ge1$, a PAC-style samplable $D$ with a coding header $\sigma_Q$, a polynomial clock $t$ adequate for $D$, constants $0<\theta_1<\theta_2\le 3/4$ and a positive polynomial $p(n)\ge1$. Then there is a PPT algorithm $B$ such that, for infinitely many $n$,
--   $$\Pr_{(x,y)\sim D_n,\,B}\Big[\mathrm{pSC}^t_{\theta_1}(x,y)\le B(1^n,x,y)\le \mathrm{pSC}^t_{\theta_2}(x,y)\Big]\ \ge\ 1-\frac{1}{p(n)} .$$
--
--   This is the easy half of the characterization on PAC-style samples: without one-way functions, an efficient algorithm finds a value between two quantiles of the shortest local certificate. The thresholds are strictly separated and the upper one is at most $3/4$, the quantile bounded by Lemma 3.3.
--
--   Differences from the source:
--   - generalization: one efficiently universal Turing machine U, fixed once and for all (§2.1, p.12) → every `Decoder`: any step-indexed machine with the clock, sequential-reading, universality and simulation properties stated in §2.1; reason: §2.1's machine has these properties, so the statement specializes to it
--   - reading: the coding header σ_Q fixed once and for all for D (Definition 3.2) → every header σQ with `IsCodingHeader` (correct whenever it halts on a long enough tape, halts within a polynomial in the program and query lengths); reason: the paper fixes the header without naming it; the result is meant for any such choice, and the polynomial halting bound is §2.1's simulation overhead
--   - encoding: polynomial schedules (m, t ≥ 1) and positive polynomials p(n) ≥ 1, t₀(n), t_D(n) → `QuantumPRC.EffPoly` schedules with m n ≥ 1, t n ≥ 1; existential or universal polynomials in ℕ[X] with values ≥ 1; reason: EffPoly is polynomially bounded and polynomial-time computable; every positive real polynomial is dominated by an ℕ[X] polynomial and the bounds are monotone in p
--   - encoding: a PPT algorithm receiving 1^n and a dataset, whose output is a binary integer or the symbol ∞ (else a failure) → `PPT`: one `CookPvsNP.PolyTimeComputable` machine on the code of (coins, input), coin count polynomial in the input length; input `datasetCode`; output read by `decodeOut`; reason: the standard uniform PPT model with fixed injective codes; no instance changes
--   - encoding: quantiles in Z≥0 ∪ {∞}; closed intervals of Z ∪ {∞} with ∞ ± d = ∞; ⌈log m⌉ → `pSC` in ℕ∞; the window in `WithTop ℤ` with shifts by `WithTop.map`; `Nat.clog 2 m`; reason: same values and the same order
--   - encoding: a concept sampler Q(1^n; r) outputting a program c_r evaluated within τ_Q(n) steps → a polynomial-time evaluator (1^n, r, z) ↦ c_r(z) (`PACSampler.conc`); reason: producing c_r in polynomial time and evaluating it in polynomial time is the same as a polynomial-time evaluator
-- source:
--   Myrisiotis, One-Way Functions and Local Descriptions of Random Data, STOC 2027 submission (held manuscript, sha256 d818fa43…4c4e), Theorem 5.1, p.24 (restatement of Theorem 1.2)

import Mathlib
import Definitions.Def_QuantumPRC_IsPolyFamily
import Definitions.Def_OWFLocalDesc_OWFExist
import Definitions.Def_OWFLocalDesc_succSampler
import Definitions.Def_OWFLocalDesc_IsCodingHeader
import Definitions.Def_OWFLocalDesc_Adequate
set_option autoImplicit false

namespace OWFLocalDesc

/-- **Theorem 5.1 (Robust easiness without one-way functions; restatement of Theorem 1.2).**
Myrisiotis, *One-Way Functions and Local Descriptions of Random Data*, STOC 2027 submission
(held manuscript, sha256 d818fa43…4c4e), Theorem 5.1, p.24: "Assume one-way functions do not exist. Fix a
polynomial sample-size schedule m(n) ≥ 1 and a PAC-style samplable D. Fix also a polynomial clock t
adequate for D, constants 0 < θ1 < θ2 ≤ 3/4, and a positive polynomial p(n) ≥ 1. There is a PPT
algorithm B = B_{D,t,p,θ1,θ2} such that, for infinitely many n,
Pr_{(x,y)∼D_n,B}[pSC^t_{θ1}(x,y) ≤ B(1^n,x,y) ≤ pSC^t_{θ2}(x,y)] ≥ 1 − 1/p(n)."

**Formalization Note.** For every decoder and every coding header `σQ` (adequacy is relative to
it). `p` has natural coefficients (every positive polynomial is dominated by one, and a larger
`p` gives a stronger bound). "For infinitely many n" is `∀ N, ∃ n ≥ N`. No tolerance (`d = 0`). -/
theorem theorem_5_1 (hno : ¬ OWFExist) (U : Decoder) (m : ℕ → ℕ) (hm : QuantumPRC.EffPoly m)
    (hm1 : ∀ n, 1 ≤ m n) (D : PACSampler) (σQ : List Bool) (hσQ : IsCodingHeader U D σQ)
    (t : ℕ → ℕ) (ht : QuantumPRC.EffPoly t) (ht1 : ∀ n, 1 ≤ t n) (hadq : Adequate U D σQ t)
    (θ₁ θ₂ : ℝ) (hθ₁ : 0 < θ₁) (hθ₁₂ : θ₁ < θ₂) (hθ₂ : θ₂ ≤ 3 / 4)
    (p : Polynomial ℕ) (hp : ∀ n, 1 ≤ p.eval n) :
    ∃ B : PPT, ∀ N : ℕ, ∃ n ≥ N,
      1 - 1 / ((p.eval n : ℕ) : ℝ) ≤ succSampler U D t m θ₁ θ₂ 0 B n := by sorry

end OWFLocalDesc
