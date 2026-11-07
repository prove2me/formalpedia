-- Prove2me | Theorems.Thm_OWFLocalDesc_corollary_5_4
-- name    : OWFLocalDesc.corollary_5_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:50:45.217109+00:00
-- url     : https://prove2.me/theorems/4852bb0f-e231-4761-bd3e-7209db185351
-- title:
--   Corollary 5.4 (Uniform-data equivalence): one-way functions exist iff estimating $\mathrm{pSC}$ of uniform data between two quantiles is hard on average
-- statement:
--   Fix a decoder $U$, a full-anchor lookup program $\sigma_L$, a polynomially bounded, polynomial-time computable schedule $m(n)\ge 8n$ and an integer $a\ge0$.
--
--   1. There is a PAC-style sampler with uniform points within total variation distance $\binom{m(n)}{2}2^{-n}$ of $D_{0,n}$ at every $n\ge1$, together with a coding header for it (this is $D_{\mathrm{ind}}$ of Lemma 4.8).
--   2. For every PAC-style sampler $D$ within that distance of $D_{0,n}$ and every coding header $\sigma_Q$ for $D$: one-way functions exist **if and only if** there are a polynomial clock $t$, adequate for $D$ and permitting full-anchor lookup, and a positive polynomial $p(n)\ge1$ such that every PPT algorithm $B$ eventually satisfies
--   $$\Pr_{(X,Y)\sim D_{0,n},\,B}\Big[\mathrm{pSC}^t_{1/2}(X,Y)-a\lceil\log m\rceil\le B(1^n,X,Y)\le\mathrm{pSC}^t_{3/4}(X,Y)+a\lceil\log m\rceil\Big]\ <\ 1-\frac1{p(n)} .$$
--
--   Here $D_{0,n}$ draws $m(n)$ independent uniform $n$-bit points with independent uniform labels, repeated points included. Specialized to $D=D_{\mathrm{ind}}$, clause 2 is the paper's characterization of one-way functions by the average-case hardness of estimating the shortest local description of random labeled data.
--
--   Differences from the source:
--   - generalization: the sampler D_ind constructed in Lemma 4.8 → every PAC-style sampler D with TV(D_n, D_{0,n}) ≤ (m(n) choose 2) 2^{−n} at every positive n, and every coding header for it; reason: the proof uses only this bound (Corollary 5.3, p.28); D_ind satisfies it by Lemma 4.8, so the statement specializes to D_ind
--   - generalization: one efficiently universal Turing machine U, fixed once and for all (§2.1, p.12) → every `Decoder`: any step-indexed machine with the clock, sequential-reading, universality and simulation properties stated in §2.1; reason: §2.1's machine has these properties, so the statement specializes to it
--   - reading: the fixed full-anchor lookup program (p.13) → every lookup program σL with `IsLookupHeader` (correct whenever it halts, halts within a polynomial in the lengths of anchor list and query); reason: the paper fixes the program without naming it; the result is meant for any such choice, and the polynomial halting bound is the running time stated on p.13
--   - reading: the coding header σ_Q fixed once and for all for D (Definition 3.2) → every header σQ with `IsCodingHeader` (correct whenever it halts on a long enough tape, halts within a polynomial in the program and query lengths); reason: the paper fixes the header without naming it; the result is meant for any such choice, and the polynomial halting bound is §2.1's simulation overhead
--   - encoding: polynomial schedules (m, t ≥ 1) and positive polynomials p(n) ≥ 1, t₀(n), t_D(n) → `QuantumPRC.EffPoly` schedules with m n ≥ 1, t n ≥ 1; existential or universal polynomials in ℕ[X] with values ≥ 1; reason: EffPoly is polynomially bounded and polynomial-time computable; every positive real polynomial is dominated by an ℕ[X] polynomial and the bounds are monotone in p
--   - encoding: a PPT algorithm receiving 1^n and a dataset, whose output is a binary integer or the symbol ∞ (else a failure) → `PPT`: one `CookPvsNP.PolyTimeComputable` machine on the code of (coins, input), coin count polynomial in the input length; input `datasetCode`; output read by `decodeOut`; reason: the standard uniform PPT model with fixed injective codes; no instance changes
--   - encoding: quantiles in Z≥0 ∪ {∞}; closed intervals of Z ∪ {∞} with ∞ ± d = ∞; ⌈log m⌉ → `pSC` in ℕ∞; the window in `WithTop ℤ` with shifts by `WithTop.map`; `Nat.clog 2 m`; reason: same values and the same order
--   - encoding: a concept sampler Q(1^n; r) outputting a program c_r evaluated within τ_Q(n) steps → a polynomial-time evaluator (1^n, r, z) ↦ c_r(z) (`PACSampler.conc`); reason: producing c_r in polynomial time and evaluating it in polynomial time is the same as a polynomial-time evaluator
-- source:
--   Myrisiotis, One-Way Functions and Local Descriptions of Random Data, STOC 2027 submission (held manuscript, sha256 d818fa43…4c4e), Corollary 5.4, p.28 (restatement of Corollary 1.4)

import Mathlib
import Definitions.Def_QuantumPRC_IsPolyFamily
import Definitions.Def_OWFLocalDesc_OWFExist
import Definitions.Def_OWFLocalDesc_succUniform
import Definitions.Def_OWFLocalDesc_HasUniformPoints
import Definitions.Def_OWFLocalDesc_tvUniform
import Definitions.Def_OWFLocalDesc_IsLookupHeader
import Definitions.Def_OWFLocalDesc_PermitsLookup
import Definitions.Def_OWFLocalDesc_IsCodingHeader
import Definitions.Def_OWFLocalDesc_Adequate
set_option autoImplicit false

namespace OWFLocalDesc

/-- **Corollary 5.4 (Uniform-data equivalence; restatement of Corollary 1.4).** Myrisiotis, *One-Way Functions and Local Descriptions of Random Data*, STOC 2027 submission
(held manuscript, sha256 d818fa43…4c4e),
Corollary 5.4, p.28: "Fix a polynomially bounded, polynomial-time computable integer schedule
m(n) ≥ 8n and an integer a ≥ 0. Let D_ind be the fixed sampler constructed in Lemma 4.8 for this
schedule. One-way functions exist if and only if the following property holds. There are a
polynomial clock t, adequate for D_ind and permitting full-anchor lookup, and a positive polynomial
p(n) ≥ 1 such that every PPT algorithm eventually has success strictly below 1 − 1/p(n) on D_{0,n}
in returning a value in [pSC^t_{1/2} − a⌈log m⌉, pSC^t_{3/4} + a⌈log m⌉]."

**Formalization Note.** For every decoder `U` and every full-anchor lookup header `σL`.
(i) Some PAC-style sampler with uniform points is within `(m(n) choose 2) 2^{−n}` of `D_{0,n}` and
has a coding header (this is `D_ind`, Lemma 4.8). (ii) For **every** sampler within that distance and
every coding header `σQ` for it, one-way functions exist iff the hardness property holds, with
"adequate" relative to `σQ`. By (i) this specializes to `D_ind`. Schedules are
`QuantumPRC.EffPoly` with `m, t ≥ 1`; `p` has natural coefficients and is fixed before the
algorithm; "eventually" is `∃ n₀, ∀ n ≥ n₀` after the algorithm; `⌈log m⌉` is `Nat.clog 2 m`. -/
theorem corollary_5_4 (U : Decoder) (σL : List Bool) (hσL : IsLookupHeader U σL)
    (m : ℕ → ℕ) (hm : QuantumPRC.EffPoly m) (hm1 : ∀ n, 1 ≤ m n) (hm8 : ∀ n, 8 * n ≤ m n)
    (a : ℕ) :
    (∃ D : PACSampler, HasUniformPoints D ∧
        (∀ n : ℕ, 0 < n → tvUniform D (m n) n ≤ ((m n).choose 2 : ℝ) / (2 : ℝ) ^ n) ∧
        ∃ σQ : List Bool, IsCodingHeader U D σQ) ∧
    ∀ D : PACSampler,
      (∀ n : ℕ, 0 < n → tvUniform D (m n) n ≤ ((m n).choose 2 : ℝ) / (2 : ℝ) ^ n) →
      ∀ σQ : List Bool, IsCodingHeader U D σQ →
        (OWFExist ↔
          ∃ t : ℕ → ℕ, QuantumPRC.EffPoly t ∧ (∀ n, 1 ≤ t n) ∧ Adequate U D σQ t ∧
            PermitsLookup U σL m t ∧
            ∃ p : Polynomial ℕ, (∀ n, 1 ≤ p.eval n) ∧
              ∀ B : PPT, ∃ n₀ : ℕ, ∀ n ≥ n₀,
                succUniform U t m (1 / 2) (3 / 4) (a * Nat.clog 2 (m n)) B n <
                  1 - 1 / ((p.eval n : ℕ) : ℝ)) := by sorry

end OWFLocalDesc
