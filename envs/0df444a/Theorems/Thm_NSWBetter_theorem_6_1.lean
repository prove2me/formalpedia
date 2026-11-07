-- Prove2me | Theorems.Thm_NSWBetter_theorem_6_1
-- name    : NSWBetter.theorem_6_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:01:31.2082+00:00
-- url     : https://prove2.me/theorems/f46ec0d0-5f30-4af2-90be-807b91d0b7ff
-- title:
--   Theorem 6.1 — the main algorithm: a constant gain under large good consistency
-- statement:
--   There are an absolute constant $c_3^*>0$, a polynomial $p$ and a randomized polynomial-time algorithm (a deterministic polynomial-time algorithm reading $p(|\langle I,y\rangle|)$ fair coins) with the following property. Let $I$ be an instance with nonnegative rational values, $y$ a configuration LP solution given by a list of its entries, and $x$ the corresponding fractional allocation. If at most $\gamma^3n$ agents are not well-behaved in $x$ and $x$ satisfies the large good consistency property, then
--   1. for every coin string the output $z$ is a fractional allocation, and
--   2. for every choice of ST rounding schemes for the outputs (Marginals, Cardinality, Rationality),
--   $$\mathbb E[\mathrm{ST}(z)]\ge\frac1n\sum_{i\in N,S\subseteq G}y_{i,S}\ln v_i(S)-\frac1e+c_3^*,$$
--   the expectation over the coins.
--
--   Differences from the source:
--   - reading: "for some constant $c_3^*>0$" → one $c_3^*$ for all instances; reason: the constant is combined uniformly in the proof of Theorem 1.1; a per-instance constant would be weaker
--   - reading: "(randomized) fractional allocation $z$", "$\mathbb E[\mathrm{ST}(z)]$" → a deterministic polynomial-time map of $(I,y,w)$ with $z$ valid for every coin string $w$ of length $p(|\langle I,y\rangle|)$, the expectation the average over all such $w$; reason: the standard model of randomized polynomial time with fair coins; the rational-probability choices of p.38 are approximated by fair coins to accuracy $2^{-\mathrm{poly}}$
--   - reading: "configuration LP solution" → rational, valid, finite objective; reason: the standing convention of p.19
--   - reading: $\mathrm{ST}(z)$ → the bound for every value order and every scheme with Marginals, Cardinality and Rationality; reason: the source allows any such rounding and fixes the order only up to ties
--   - reading: "not well-behaved" → Definition 4.14 with every $\Delta\ge1$ making all $\Delta x_{ig}$ integral; reason: by Lemma 4.12 the same predicate for rational $x$
--   - encoding: "polynomial time algorithm" → `Turing.TM2ComputableInPolyTime` over fixed binary encodings, $y$ as a list of entries, $z$ as a row-major list of rationals; reason: Mathlib's Turing-machine model; the validity of $z$ is part of the conclusion
--   - encoding: the random matching and $\mathrm{ST}(z)$ → a finitely supported distribution on matchings, `ST` in `EReal`; reason: same values whenever finite
-- source:
--   Viswanathan, A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations, arXiv:2607.13340 (held version, sha256 08811cb468c2df39231dca4222c5af94163587c7c83e205e50bbf0b91fc1deb3), Theorem 6.1, p.36

import Mathlib
import Definitions.Def_ReserveLB_encRatList
import Definitions.Def_NSWBetter_Inst
import Definitions.Def_NSWBetter_Inst_WellFormed
import Definitions.Def_NSWBetter_Inst_rv
import Definitions.Def_NSWBetter_coinAvgE
import Definitions.Def_NSWBetter_gamma
import Definitions.Def_NSWBetter_IsFrac
import Definitions.Def_NSWBetter_IsCLPSolution
import Definitions.Def_NSWBetter_lpVal
import Definitions.Def_NSWBetter_corrFrac
import Definitions.Def_NSWBetter_IsValueOrder
import Definitions.Def_NSWBetter_IsSTScheme
import Definitions.Def_NSWBetter_IsRationalScheme
import Definitions.Def_NSWBetter_ST
import Definitions.Def_NSWBetter_Nnwb
import Definitions.Def_NSWBetter_LGC
import Definitions.Def_NSWBetter_Entry
import Definitions.Def_NSWBetter_encInstEntries
import Definitions.Def_NSWBetter_encInstEntriesCoins
import Definitions.Def_NSWBetter_decodeFrac
import Definitions.Def_NSWBetter_decodeCLP

namespace NSWBetter

/-- **Theorem 6.1 — the main algorithm.**
Viswanathan, *A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations*, arXiv:2607.13340 (held version, sha256 08811cb4…), Theorem 6.1, p.36: "Let y be a configuration LP solution, and let x be the corresponding fractional allocation. If at most γ³n agents are not well-behaved in x and x satisfies the large good consistency property, then there is a polynomial time algorithm that outputs a (randomized) fractional allocation z such that E[ST(z)] ≥ (1/n) Σ_(i∈N,S⊆G) yi,S ln(vi(S)) − 1/e + c∗3, for some constant c∗3 > 0."

There are an absolute constant `c₃ > 0`, a polynomial `p` and a Turing machine, polynomial time in the binary encoding of `(I, entries of y, coins)`, such that: for every coin string `w` of length `p(|enc(I, y)|)` the output decodes to a fractional allocation `z_w`, and for every family of ST rounding schemes `D_w` of the `z_w`, the average of `ST(z_w)` over all coin strings is at least the bound.

**Formalization Note.** Randomness is a uniform coin string of fixed polynomial length given to a deterministic machine. -/
theorem theorem_6_1 :
    ∃ c₃ : ℝ, 0 < c₃ ∧ ∃ (p : Polynomial ℕ) (A : (Inst × List Entry) × List Bool → List ℚ),
      Nonempty (Turing.TM2ComputableInPolyTime encInstEntriesCoins ReserveLB.encRatList A) ∧
      ∀ I : Inst, I.WellFormed → ∀ l : List Entry,
        IsCLPSolution I.rv (decodeCLP I l) →
        ((Nnwb I.rv (corrFrac (decodeCLP I l))).card : ℝ) ≤ gamma ^ 3 * I.n →
        LGC I.rv (corrFrac (decodeCLP I l)) →
        (∀ w : List Bool, w.length = p.eval (encInstEntries (I, l)).length →
          IsFrac (fun i g => ((decodeFrac I (A ((I, l), w)) i g : ℚ) : ℝ))) ∧
        ∀ r : Fin I.n → Fin I.m ≃ Fin I.m, IsValueOrder I.rv r →
        ∀ D : List Bool → Finset (Fin I.n × Fin I.m × Fin I.m) → ℝ,
          (∀ w : List Bool, w.length = p.eval (encInstEntries (I, l)).length →
            IsSTScheme r (fun i g => ((decodeFrac I (A ((I, l), w)) i g : ℚ) : ℝ)) (D w) ∧
            IsRationalScheme (D w)) →
          ((lpVal I.rv (decodeCLP I l) - 1 / Real.exp 1 + c₃ : ℝ) : EReal) ≤
            coinAvgE (p.eval (encInstEntries (I, l)).length) (fun w => ST I.rv (D w)) := by sorry

end NSWBetter
