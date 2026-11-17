-- Prove2me | Theorems.Thm_OWFLocalDesc_Supplement_theorem_4_6
-- name    : OWFLocalDesc.Supplement.theorem_4_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T16:58:46.053204+00:00
-- url     : https://prove2.me/theorems/b9970fbe-ddbb-4260-b1aa-f64db3198b94
-- title:
--   Theorem 4.6 — unconditional uniform-label estimation with tolerance in binary
-- statement:
--   Fix a decoder $U$ and a full-anchor lookup program $\sigma_L$ for it, a polynomial sample schedule $m(n)\ge1$, a polynomial clock $t(n)\ge1$ that permits full-anchor lookup with $\sigma_L$, and constants $0<\theta_1\le\theta_2\le1$. Write $c_{\mathrm{lookup}}=|\sigma_L|$.
--
--   There is a deterministic polynomial-time estimator $E$, which receives $(1^n,x,y,d)$ with the tolerance $d$ in binary, such that for every point length $n\ge1$ and every integer tolerance $d\ge0$
--   $$\Pr_{(X,Y)\sim D_{0,n}}\Big[E(1^n,X,Y,d)\notin\big[\mathrm{pSC}^t_{\theta_1}(X,Y)-d,\ \mathrm{pSC}^t_{\theta_2}(X,Y)+d\big]\Big]\ \le\ \min\Big\{1,\ \frac{2^{c_{\mathrm{lookup}}+1}(m(n)+1)}{\theta_2}\,2^{-2d}\Big\}.$$
--   Here $D_{0,n}$ draws $m(n)$ independent uniform $n$-bit points and $m(n)$ independent uniform labels.
--
--   No cryptographic assumption is needed. With a tolerance of order $\log m+\log p$, the error is at most $1/p(n)$, which locates the precision–error tradeoff of Theorem 4.5 at a logarithmic scale.
--
--   Differences from the source:
--   - generalization: one efficiently universal Turing machine U, fixed once and for all (§2.1, p.12) → every `Decoder`: any step-indexed machine with the clock, sequential-reading, universality and simulation properties stated in §2.1; reason: §2.1's machine has these properties, so the statement specializes to it
--   - reading: "There is a constant c_lookup" (the proof: "A fixed program implementing full-anchor lookup has length c_lookup") → c_lookup is σL.length, the length of the lookup header σL that the clock permits; reason: an unconstrained ∃ c_lookup makes the bound min{1, …} = 1 for large c and the theorem empty; the proof's constant is the program length, and fixing it is the stronger reading
--   - reading: "the" full-anchor lookup program of §2.1, p.13 → every header σL with `IsLookupHeader U σL`, and `PermitsLookup U σL m t`; reason: the paper fixes the program without naming it; the result is meant for any such choice (as in the published Theorem 4.5)
--   - encoding: every polynomial-time computable nonnegative integer tolerance d(n) of polynomial bit length → ∀ n ≥ 1, ∀ d : ℕ (the estimator fixed before n and d); reason: the bound at n involves only d(n), and every value d at n is taken by a constant schedule, which qualifies
--   - encoding: a deterministic polynomial-time estimator taking (1^n, x, y, d(n)), d in binary; failure probability on independent uniform points and labels → E : List Bool → List Bool with `CookPvsNP.PolyTimeComputable E` on `tolInput x y d` (datasetCode, then `Nat.bits d`); `estFail` counts failing datasets over 2^{m(n)n+m(n)}; reason: the published deterministic machine model and the uniform measure of D_{0,n}; no instance changes
--   - encoding: polynomial schedules m(n) ≥ 1, t(n) ≥ 1 → `QuantumPRC.EffPoly` schedules with m n ≥ 1, t n ≥ 1; reason: EffPoly is polynomially bounded and polynomial-time computable, exactly the paper's polynomial schedules
--   - encoding: quantiles in Z≥0 ∪ {∞}; closed intervals of Z ∪ {∞} with ∞ ± d = ∞; ⌈log m⌉ → `pSC` in ℕ∞; `InInterval` in `WithTop ℤ`; `Nat.clog 2`; reason: same values and the same order
-- source:
--   Myrisiotis, One-Way Functions and Local Descriptions of Random Data, STOC 2027 submission (held manuscript, sha256 d818fa43…4c4e), Theorem 4.6, p.22

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_QuantumPRC_IsPolyFamily
import Definitions.Def_OWFLocalDesc_IsLookupHeader
import Definitions.Def_OWFLocalDesc_PermitsLookup
import Definitions.Def_OWFLocalDesc_Supplement_estFail
set_option autoImplicit false

namespace OWFLocalDesc.Supplement

open OWFLocalDesc

/-- **Theorem 4.6 (Uniform-label estimation).** Myrisiotis, *One-Way Functions and Local
Descriptions of Random Data*, STOC 2027 submission (held manuscript, sha256 d818fa43…4c4e),
Theorem 4.6, p.22: "Fix a polynomial sample schedule m, a polynomial clock t permitting
full-anchor lookup, and constants 0 < θ1 ≤ θ2 ≤ 1. There is a constant c_lookup and a deterministic
polynomial-time estimator taking (1^n,x,y,d(n)) as input, with the tolerance supplied in binary,
with the following property. For every polynomial-time computable nonnegative integer tolerance
d(n) of polynomial bit length, its probability of failing to return a value in
[pSC^t_{θ1}(X,Y) − d(n), pSC^t_{θ2}(X,Y) + d(n)] on independent uniform points and labels is at
most min{1, 2^{c_lookup+1}(m(n)+1)/θ2 · 2^{−2d(n)}}."

**Formalization Note.**
1. For every decoder `U` and every full-anchor lookup header `σL`; "permitting full-anchor lookup"
   is the published `PermitsLookup U σL m t`. The constant `c_lookup` is the length of the lookup
   program, `σL.length` (proof, p.22: "A fixed program implementing full-anchor lookup has length
   c_lookup"); an unconstrained `∃ c_lookup` would make the bound `1` and the claim empty.
2. The estimator is a deterministic `CookPvsNP.PolyTimeComputable` map on `(1ⁿ, x, y, d)`
   (`tolInput`, `d` in binary), fixed before `n` and `d`.
3. "Every tolerance schedule d(n)" is `∀ n ≥ 1, ∀ d : ℕ`: the bound at `n` involves only `d(n)`,
   and every value `d` at `n` is taken by a constant schedule, which qualifies.
4. Schedules are `QuantumPRC.EffPoly` with the standing `m, t ≥ 1` (§2.1, p.12); points have
   `n ≥ 1` bits. The bound holds at every such `n`, with no one-way-function hypothesis. -/
theorem theorem_4_6 (U : Decoder) (σL : List Bool) (hσL : IsLookupHeader U σL)
    (m : ℕ → ℕ) (hm : QuantumPRC.EffPoly m) (hm1 : ∀ n, 1 ≤ m n)
    (t : ℕ → ℕ) (ht : QuantumPRC.EffPoly t) (ht1 : ∀ n, 1 ≤ t n) (hlook : PermitsLookup U σL m t)
    (θ₁ θ₂ : ℝ) (hθ₁ : 0 < θ₁) (hθ₁₂ : θ₁ ≤ θ₂) (hθ₂ : θ₂ ≤ 1) :
    ∃ E : List Bool → List Bool, CookPvsNP.PolyTimeComputable E ∧
      ∀ n : ℕ, 0 < n → ∀ d : ℕ,
        estFail U E t m θ₁ θ₂ d n ≤
          min 1 ((2 : ℝ) ^ (σL.length + 1) * ((m n : ℝ) + 1) / θ₂ * ((2 : ℝ) ^ (2 * d))⁻¹) := by sorry

end OWFLocalDesc.Supplement
