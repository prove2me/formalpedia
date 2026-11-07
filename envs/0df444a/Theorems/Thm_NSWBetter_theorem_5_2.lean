-- Prove2me | Theorems.Thm_NSWBetter_theorem_5_2
-- name    : NSWBetter.theorem_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:02:13.6373+00:00
-- url     : https://prove2.me/theorems/eba647f9-8930-4897-b5ef-9694f7d9ace5
-- title:
--   Theorem 5.2 — a constant gain when large good consistency fails
-- statement:
--   There are an absolute constant $c_2^*\in(0,1)$ and a deterministic polynomial-time algorithm with the following property. Let $I$ be an instance with nonnegative rational values, $y$ a configuration LP solution given by a list of its entries, and $x$ the corresponding fractional allocation. If at most $\gamma^3n$ agents are not well-behaved in $x$ and $x$ does not satisfy the large good consistency property, then the algorithm, on input $(I,y)$, outputs a fractional allocation $z$ such that for every ST rounding scheme for $z$ (Marginals, Cardinality, Rationality),
--   $$\mathrm{ST}(z)\ge\frac1n\sum_{i\in N,S\subseteq G}y_{i,S}\ln v_i(S)-\frac1e+c_2^* .$$
--
--   Differences from the source:
--   - reading: "for some constant $c_2^*\in(0,1)$" → one $c_2^*$ for all instances; reason: the constant is combined uniformly in the proof of Theorem 1.1; a per-instance constant would be weaker
--   - reading: "configuration LP solution" → rational, valid, finite objective; reason: the standing convention of p.19
--   - reading: $\mathrm{ST}(z)$ → the bound for every value order and every scheme with Marginals, Cardinality and Rationality; reason: the source allows any such rounding and fixes the order only up to ties
--   - reading: "not well-behaved" → Definition 4.14 with every $\Delta\ge1$ making all $\Delta x_{ig}$ integral; reason: by Lemma 4.12 the same predicate for rational $x$
--   - encoding: "polynomial time algorithm" on $(I,y)$ → `Turing.TM2ComputableInPolyTime` over fixed binary encodings, $y$ as a list of entries, $z$ output as a row-major list of rationals; reason: Mathlib's Turing-machine model; the validity of $z$ is part of the conclusion
--   - encoding: the random matching and $\mathrm{ST}(z)$ → a finitely supported distribution on matchings, `ST` in `EReal`; reason: same values whenever finite
-- source:
--   Viswanathan, A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations, arXiv:2607.13340 (held version, sha256 08811cb468c2df39231dca4222c5af94163587c7c83e205e50bbf0b91fc1deb3), Theorem 5.2, p.28

import Mathlib
import Definitions.Def_ReserveLB_encRatList
import Definitions.Def_NSWBetter_Inst
import Definitions.Def_NSWBetter_Inst_WellFormed
import Definitions.Def_NSWBetter_Inst_rv
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
import Definitions.Def_NSWBetter_decodeFrac
import Definitions.Def_NSWBetter_decodeCLP

namespace NSWBetter

/-- **Theorem 5.2.**
Viswanathan, *A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations*, arXiv:2607.13340 (held version, sha256 08811cb4…), Theorem 5.2, p.28: "Let y be a configuration LP solution for an instance I, and let x be the corresponding fractional allocation. If at most γ³n agents are not well-behaved in x and x does not satisfy the large good consistency property, then there is a polynomial time algorithm that outputs a fractional allocation z such that ST(z) ≥ (1/n) Σ_(i∈N,S⊆G) yi,S ln(vi(S)) − 1/e + c∗2, for some constant c∗2 ∈ (0, 1)."

There are an absolute constant `c₂ ∈ (0, 1)` and a deterministic Turing machine, polynomial time in the binary encoding of `(I, entries of y)`, whose output decodes to a fractional allocation `z` with the stated bound for every ST rounding scheme of `z`.

**Formalization Note.** `y` is given by any list of entries that decodes to a configuration LP solution. The validity of `z` is part of the conclusion. -/
theorem theorem_5_2 :
    ∃ c₂ : ℝ, 0 < c₂ ∧ c₂ < 1 ∧ ∃ A : Inst × List Entry → List ℚ,
      Nonempty (Turing.TM2ComputableInPolyTime encInstEntries ReserveLB.encRatList A) ∧
      ∀ I : Inst, I.WellFormed → ∀ l : List Entry,
        IsCLPSolution I.rv (decodeCLP I l) →
        ((Nnwb I.rv (corrFrac (decodeCLP I l))).card : ℝ) ≤ gamma ^ 3 * I.n →
        ¬ LGC I.rv (corrFrac (decodeCLP I l)) →
        IsFrac (fun i g => ((decodeFrac I (A (I, l)) i g : ℚ) : ℝ)) ∧
        ∀ r : Fin I.n → Fin I.m ≃ Fin I.m, IsValueOrder I.rv r →
        ∀ D : Finset (Fin I.n × Fin I.m × Fin I.m) → ℝ,
          IsSTScheme r (fun i g => ((decodeFrac I (A (I, l)) i g : ℚ) : ℝ)) D →
          IsRationalScheme D →
          ((lpVal I.rv (decodeCLP I l) - 1 / Real.exp 1 + c₂ : ℝ) : EReal) ≤ ST I.rv D := by sorry

end NSWBetter
