-- Prove2me | Theorems.Thm_OWFLocalDesc_corollary_5_3
-- name    : OWFLocalDesc.corollary_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:50:28.33543+00:00
-- url     : https://prove2.me/theorems/bd32fee3-b50a-42e0-8e02-153ffdc6c358
-- title:
--   Corollary 5.3 (Uniform-data easiness without one-way functions)
-- statement:
--   Assume one-way functions do not exist. Fix a decoder $U$, a polynomial schedule $m(n)\ge1$, a PAC-style sampler $D$ with
--   $$\mathrm{TV}(D_n,D_{0,n})\le\binom{m(n)}{2}2^{-n}\qquad(n\ge1)$$
--   (for instance $D_{\mathrm{ind}}$ of Lemma 4.8) and a coding header $\sigma_Q$ for it, a polynomial clock $t$ adequate for $D$, constants $0<\theta_1<\theta_2\le3/4$ and a positive polynomial $p(n)\ge1$. Then some PPT algorithm $B$ has, for infinitely many $n$,
--   $$\Pr_{(X,Y)\sim D_{0,n},\,B}\Big[\mathrm{pSC}^t_{\theta_1}(X,Y)\le B(1^n,X,Y)\le\mathrm{pSC}^t_{\theta_2}(X,Y)\Big]\ \ge\ 1-\frac1{p(n)} .$$
--
--   This is the easy half of the uniform-data characterization (Corollary 5.4).
--
--   Differences from the source:
--   - generalization: the sampler D_ind constructed in Lemma 4.8 → every PAC-style sampler D with TV(D_n, D_{0,n}) ≤ (m(n) choose 2) 2^{−n} at every positive n, and every coding header for it; reason: the proof uses only this bound (Corollary 5.3, p.28); D_ind satisfies it by Lemma 4.8, so the statement specializes to D_ind
--   - generalization: one efficiently universal Turing machine U, fixed once and for all (§2.1, p.12) → every `Decoder`: any step-indexed machine with the clock, sequential-reading, universality and simulation properties stated in §2.1; reason: §2.1's machine has these properties, so the statement specializes to it
--   - reading: the coding header σ_Q fixed once and for all for D (Definition 3.2) → every header σQ with `IsCodingHeader` (correct whenever it halts on a long enough tape, halts within a polynomial in the program and query lengths); reason: the paper fixes the header without naming it; the result is meant for any such choice, and the polynomial halting bound is §2.1's simulation overhead
--   - encoding: polynomial schedules (m, t ≥ 1) and positive polynomials p(n) ≥ 1, t₀(n), t_D(n) → `QuantumPRC.EffPoly` schedules with m n ≥ 1, t n ≥ 1; existential or universal polynomials in ℕ[X] with values ≥ 1; reason: EffPoly is polynomially bounded and polynomial-time computable; every positive real polynomial is dominated by an ℕ[X] polynomial and the bounds are monotone in p
--   - encoding: a PPT algorithm receiving 1^n and a dataset, whose output is a binary integer or the symbol ∞ (else a failure) → `PPT`: one `CookPvsNP.PolyTimeComputable` machine on the code of (coins, input), coin count polynomial in the input length; input `datasetCode`; output read by `decodeOut`; reason: the standard uniform PPT model with fixed injective codes; no instance changes
--   - encoding: quantiles in Z≥0 ∪ {∞}; closed intervals of Z ∪ {∞} with ∞ ± d = ∞; ⌈log m⌉ → `pSC` in ℕ∞; the window in `WithTop ℤ` with shifts by `WithTop.map`; `Nat.clog 2 m`; reason: same values and the same order
--   - encoding: a concept sampler Q(1^n; r) outputting a program c_r evaluated within τ_Q(n) steps → a polynomial-time evaluator (1^n, r, z) ↦ c_r(z) (`PACSampler.conc`); reason: producing c_r in polynomial time and evaluating it in polynomial time is the same as a polynomial-time evaluator
-- source:
--   Myrisiotis, One-Way Functions and Local Descriptions of Random Data, STOC 2027 submission (held manuscript, sha256 d818fa43…4c4e), Corollary 5.3, p.28

import Mathlib
import Definitions.Def_QuantumPRC_IsPolyFamily
import Definitions.Def_OWFLocalDesc_OWFExist
import Definitions.Def_OWFLocalDesc_succUniform
import Definitions.Def_OWFLocalDesc_tvUniform
import Definitions.Def_OWFLocalDesc_IsCodingHeader
import Definitions.Def_OWFLocalDesc_Adequate
set_option autoImplicit false

namespace OWFLocalDesc

/-- **Corollary 5.3 (Uniform-data easiness).** Myrisiotis, *One-Way Functions and Local Descriptions of Random Data*, STOC 2027 submission
(held manuscript, sha256 d818fa43…4c4e), Corollary 5.3,
p.28: "Assume one-way functions do not exist. Fix a polynomial schedule m, the sampler D_ind from
Lemma 4.8, a polynomial clock t adequate for that sampler, constants 0 < θ1 < θ2 ≤ 3/4, and a
positive polynomial p(n) ≥ 1. Some PPT algorithm B has, for infinitely many n,
Pr_{D_{0,n},B}[pSC^t_{θ1}(X,Y) ≤ B(1^n,X,Y) ≤ pSC^t_{θ2}(X,Y)] ≥ 1 − 1/p(n)."

**Formalization Note.** Stated for every PAC-style sampler `D` with
`TV(D_n, D_{0,n}) ≤ (m(n) choose 2) 2^{−n}` at every positive point length, the property of
`D_ind` that the proof uses (Lemma 4.8 supplies such a `D`), for every decoder and every coding
header `σQ`. -/
theorem corollary_5_3 (hno : ¬ OWFExist) (U : Decoder) (m : ℕ → ℕ) (hm : QuantumPRC.EffPoly m)
    (hm1 : ∀ n, 1 ≤ m n) (D : PACSampler)
    (hD : ∀ n : ℕ, 0 < n → tvUniform D (m n) n ≤ ((m n).choose 2 : ℝ) / (2 : ℝ) ^ n)
    (σQ : List Bool) (hσQ : IsCodingHeader U D σQ)
    (t : ℕ → ℕ) (ht : QuantumPRC.EffPoly t) (ht1 : ∀ n, 1 ≤ t n) (hadq : Adequate U D σQ t)
    (θ₁ θ₂ : ℝ) (hθ₁ : 0 < θ₁) (hθ₁₂ : θ₁ < θ₂) (hθ₂ : θ₂ ≤ 3 / 4)
    (p : Polynomial ℕ) (hp : ∀ n, 1 ≤ p.eval n) :
    ∃ B : PPT, ∀ N : ℕ, ∃ n ≥ N,
      1 - 1 / ((p.eval n : ℕ) : ℝ) ≤ succUniform U t m θ₁ θ₂ 0 B n := by sorry

end OWFLocalDesc
