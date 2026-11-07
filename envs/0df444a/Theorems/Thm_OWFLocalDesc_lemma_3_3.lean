-- Prove2me | Theorems.Thm_OWFLocalDesc_lemma_3_3
-- name    : OWFLocalDesc.lemma_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:48:18.70677+00:00
-- url     : https://prove2.me/theorems/ffb486d2-d0b9-4f98-a3f4-cc514ae13e38
-- title:
--   Lemma 3.3 (PAC-style coding): $\mathrm{pSC}^t_{3/4}\le\log\frac1{D(y|x)}+\lceil\log(m+1)\rceil+c_Q+3$, and adequate clocks exist
-- statement:
--   Fix a decoder $U$, a PAC-style sampler $D=(\mu,Q)$ and a coding header $\sigma_Q$ for $D$, of length $c_Q=|\sigma_Q|$.
--
--   1. For every adequate polynomial clock $t$ and every supported dataset $(x,y)$ (with $m\ge1$ points of positive length $n$), the quantile $\mathrm{pSC}^t_{3/4}(x,y)$ is finite and
--   $$\mathrm{pSC}^t_{3/4}(x,y)\ \le\ \log\frac{1}{D(y\mid x)}+\lceil\log(m+1)\rceil+c_Q+3 .$$
--   2. Adequate schedules exist: some polynomial $t_D$ makes every polynomial schedule $t\ge t_D$ adequate.
--
--   The coding bound says that data labeled by an efficiently sampled concept have short local certificates on three quarters of the public tapes; it is the domination step of the easiness direction (Theorem 5.1), and clause 2 supplies the clock of the goal's forward direction.
--
--   Differences from the source:
--   - generalization: one efficiently universal Turing machine U, fixed once and for all (§2.1, p.12) → every `Decoder`: any step-indexed machine with the clock, sequential-reading, universality and simulation properties stated in §2.1; reason: §2.1's machine has these properties, so the statement specializes to it
--   - reading: the coding header σ_Q fixed once and for all for D (Definition 3.2) → every header σQ with `IsCodingHeader` (correct whenever it halts on a long enough tape, halts within a polynomial in the program and query lengths); reason: the paper fixes the header without naming it; the result is meant for any such choice, and the polynomial halting bound is §2.1's simulation overhead
--   - encoding: polynomial schedules (m, t ≥ 1) and positive polynomials p(n) ≥ 1, t₀(n), t_D(n) → `QuantumPRC.EffPoly` schedules with m n ≥ 1, t n ≥ 1; existential or universal polynomials in ℕ[X] with values ≥ 1; reason: EffPoly is polynomially bounded and polynomial-time computable; every positive real polynomial is dominated by an ℕ[X] polynomial and the bounds are monotone in p
--   - encoding: a concept sampler Q(1^n; r) outputting a program c_r evaluated within τ_Q(n) steps → a polynomial-time evaluator (1^n, r, z) ↦ c_r(z) (`PACSampler.conc`); reason: producing c_r in polynomial time and evaluating it in polynomial time is the same as a polynomial-time evaluator
--   - encoding: quantiles in Z≥0 ∪ {∞}; closed intervals of Z ∪ {∞} with ∞ ± d = ∞; ⌈log m⌉ → `pSC` in ℕ∞; the window in `WithTop ℤ` with shifts by `WithTop.map`; `Nat.clog 2 m`; reason: same values and the same order
-- source:
--   Myrisiotis, One-Way Functions and Local Descriptions of Random Data, STOC 2027 submission (held manuscript, sha256 d818fa43…4c4e), Lemma 3.3, p.15

import Mathlib
import Definitions.Def_QuantumPRC_IsPolyFamily
import Definitions.Def_OWFLocalDesc_pSC
import Definitions.Def_OWFLocalDesc_datasetMass
import Definitions.Def_OWFLocalDesc_IsCodingHeader
import Definitions.Def_OWFLocalDesc_Adequate
set_option autoImplicit false

namespace OWFLocalDesc

/-- **Lemma 3.3 (PAC-style coding).** Myrisiotis, *One-Way Functions and Local Descriptions of Random Data*, STOC 2027 submission
(held manuscript, sha256 d818fa43…4c4e), Lemma 3.3, p.15: "Fix a
PAC-style sampler D = (µ, Q), with σ_Q and c_Q as in Definition 3.2. For every adequate t and every
supported dataset, pSC^t_{3/4}(x,y) ≤ log(1/D(y|x)) + ⌈log(m+1)⌉ + c_Q + 3. Adequate schedules exist:
some polynomial t_D makes every polynomial schedule t ≥ t_D adequate."

**Formalization Note.** For every decoder and every coding header `σ` (`c_Q = |σ|`). "Supported"
is positive mass under `D_n`; the quantile is then finite, and `log` is the real `log₂`. Point
lengths are positive and `m, t ≥ 1` (§2, pp.11–12). `t_D` is a polynomial with natural
coefficients. -/
theorem lemma_3_3 (U : Decoder) (D : PACSampler) (σ : List Bool) (hσ : IsCodingHeader U D σ) :
    (∀ t : ℕ → ℕ, QuantumPRC.EffPoly t → (∀ n, 1 ≤ t n) → Adequate U D σ t →
      ∀ (m n : ℕ), 1 ≤ m → 0 < n → ∀ (x : Fin m → Fin n → Bool) (y : Fin m → Bool),
        0 < datasetMass D x y →
          ∃ s : ℕ, pSC U (t n) (3 / 4) x y = (s : ℕ∞) ∧
            (s : ℝ) ≤ Real.logb 2 (1 / condProb D x y) + (Nat.clog 2 (m + 1) : ℝ) +
              (σ.length : ℝ) + 3) ∧
    ∃ tD : Polynomial ℕ, ∀ t : ℕ → ℕ, QuantumPRC.EffPoly t → (∀ n, tD.eval n ≤ t n) →
      Adequate U D σ t := by sorry

end OWFLocalDesc
