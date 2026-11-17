-- Prove2me | Theorems.Thm_OWFLocalDesc_Supplement_theorem_6_2
-- name    : OWFLocalDesc.Supplement.theorem_6_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T16:59:48.697726+00:00
-- url     : https://prove2.me/theorems/184858af-e965-43be-88ec-c5fb2abf0604
-- title:
--   Theorem 6.2 — large-gap robust hardness on PAC-style samples from one-way functions
-- statement:
--   Assume one-way functions exist. Fix a decoder $U$ and a polynomial sample-size schedule $m(n)\ge 8n$ (with $m(n)\ge1$).
--
--   Then there is a PAC-style samplable distribution $D$ that has a coding header with the following property. For every coding header $\sigma_Q$ of $D$ there is a polynomial clock $t$ adequate for $D$ such that every PPT algorithm $B$ satisfies, for all sufficiently large $n$,
--   $$\Pr_{(x,y)\sim D_n,\ B}\Big[\mathrm{pSC}^t_{1/2}(x,y)-\tfrac{m}{4}\ \le\ B(1^n,x,y)\ \le\ \mathrm{pSC}^t_{3/4}(x,y)+\tfrac{m}{4}\Big]\ <\ 0.9 .$$
--
--   With Theorem 5.1 this gives Corollary 6.3: one-way functions exist iff some PAC-style sample makes estimating a value between two quantiles hard, even with a linear additive gap.
--
--   Differences from the source:
--   - generalization: one efficiently universal Turing machine U, fixed once and for all (§2.1, p.12) → every `Decoder`: any step-indexed machine with the clock, sequential-reading, universality and simulation properties stated in §2.1; reason: §2.1's machine has these properties, so the statement specializes to it
--   - reading: the coding header σ_Q fixed once and for all for D (Definition 3.2), adequacy relative to it → every header σQ with `IsCodingHeader U D σQ`; reason: the paper fixes the header without naming it; the result is meant for any such choice (as in the published Theorem 5.1)
--   - encoding: real tolerance m/4 around integer-or-∞ quantiles → natural-number tolerance m n / 4 = ⌊m/4⌋ in the published `succSampler`; reason: for integers h and o, h − m/4 ≤ o iff h − ⌊m/4⌋ ≤ o (and symmetrically above); ∞ ± d = ∞ either way
--   - encoding: there is a polynomial clock t adequate for D → D has a coding header, and for every coding header σQ of D there is an EffPoly t ≥ 1 with `Adequate U D σQ t`; reason: adequacy is defined relative to the header; the existence clause keeps the universal clause from being vacuous
--   - encoding: polynomial schedules m(n) ≥ 1, t(n) ≥ 1 → `QuantumPRC.EffPoly` schedules with m n ≥ 1, t n ≥ 1; reason: EffPoly is polynomially bounded and polynomial-time computable, exactly the paper's polynomial schedules
--   - encoding: a PPT algorithm receiving 1^n and a dataset (and a tolerance or grid index), whose output is a binary integer or the symbol ∞ (else a failure) → published `PPT` on `datasetCode` (followed by the extra argument in binary); output read by `decodeOut`; reason: the mission's published uniform PPT model and fixed injective codes; no instance changes
--   - encoding: quantiles in Z≥0 ∪ {∞}; closed intervals of Z ∪ {∞} with ∞ ± d = ∞; ⌈log m⌉ → `pSC` in ℕ∞; `InInterval` in `WithTop ℤ`; `Nat.clog 2`; reason: same values and the same order
-- source:
--   Myrisiotis, One-Way Functions and Local Descriptions of Random Data, STOC 2027 submission (held manuscript, sha256 d818fa43…4c4e), Theorem 6.2, p.29 (restatement of Theorem 1.3)

import Mathlib
import Definitions.Def_QuantumPRC_IsPolyFamily
import Definitions.Def_OWFLocalDesc_OWFExist
import Definitions.Def_OWFLocalDesc_succSampler
import Definitions.Def_OWFLocalDesc_IsCodingHeader
import Definitions.Def_OWFLocalDesc_Adequate
set_option autoImplicit false

namespace OWFLocalDesc.Supplement

open OWFLocalDesc

/-- **Theorem 6.2 (Large-gap robust hardness from one-way functions; restatement of Theorem
1.3).** Myrisiotis, *One-Way Functions and Local Descriptions of Random Data*, STOC 2027
submission (held manuscript, sha256 d818fa43…4c4e), Theorem 6.2, p.29: "Assume one-way functions
exist and fix a polynomial sample-size schedule m(n) ≥ 8n. There are a PAC-style samplable D and a
polynomial clock t adequate for D such that every PPT B satisfies, for all sufficiently large n,
Pr_{D_n,B}[pSC^t_{1/2}(x,y) − m/4 ≤ B(1^n,x,y) ≤ pSC^t_{3/4}(x,y) + m/4] < 0.9."

**Formalization Note.**
1. For every decoder `U`. The sampler `D` has a coding header, and for **every** coding header
   `σQ` of `D` (adequacy is relative to it, Definition 3.2) there is an adequate clock; the
   existence clause keeps the universal one from being vacuous.
2. The tolerance `m/4` is real, but quantiles and well-formed outputs are integers or `∞`, so
   `h − m/4 ≤ o ≤ h′ + m/4` is `h − ⌊m/4⌋ ≤ o ≤ h′ + ⌊m/4⌋`; `m n / 4` (natural division) in the
   published `succSampler` is therefore exact.
3. "For all sufficiently large n" is `∃ n₀, ∀ n ≥ n₀`, with `n₀` chosen after `B`; `0.9` is
   `9/10`, strict. Schedules are `QuantumPRC.EffPoly` with the standing `m, t ≥ 1`. -/
theorem theorem_6_2 (hOWF : OWFExist) (U : Decoder) (m : ℕ → ℕ) (hm : QuantumPRC.EffPoly m)
    (hm1 : ∀ n, 1 ≤ m n) (hm8 : ∀ n, 8 * n ≤ m n) :
    ∃ D : PACSampler, (∃ σQ : List Bool, IsCodingHeader U D σQ) ∧
      ∀ σQ : List Bool, IsCodingHeader U D σQ →
        ∃ t : ℕ → ℕ, QuantumPRC.EffPoly t ∧ (∀ n, 1 ≤ t n) ∧ Adequate U D σQ t ∧
          ∀ B : PPT, ∃ n₀ : ℕ, ∀ n ≥ n₀,
            succSampler U D t m (1 / 2) (3 / 4) (m n / 4) B n < 9 / 10 := by sorry

end OWFLocalDesc.Supplement
