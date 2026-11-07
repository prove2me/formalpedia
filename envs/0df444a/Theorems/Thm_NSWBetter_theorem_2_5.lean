-- Prove2me | Theorems.Thm_NSWBetter_theorem_2_5
-- name    : NSWBetter.theorem_2_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:54:48.754963+00:00
-- url     : https://prove2.me/theorems/1a193e9a-18f4-485c-820e-71dbe4070e2c
-- title:
--   Theorem 2.5 ([FL25]) — the configuration LP within $\ln(1+\varepsilon)$ in time polynomial in the input and $1/\varepsilon$
-- statement:
--   Let $I$ be an instance with $n\ge1$ agents and nonnegative rational values. There is a single algorithm which, given $I$ in binary and an integer $K\ge1$ in unary (so $\varepsilon=1/K$), runs in time polynomial in its input length (that is, in the input size and $1/\varepsilon$) and outputs a list of entries $(i,S,q)$ describing a rational vector $y$ such that
--   1. $y$ is a valid solution of the configuration LP: $\sum_Sy_{i,S}=1$ for every agent, $\sum_i\sum_{S\ni g}y_{i,S}=1$ for every good, $y\ge0$;
--   2. for every valid solution $y'$ with a finite objective, $y$ also has a finite objective and
--   $$\frac1n\sum_{i,S}y_{i,S}\ln v_i(S)\ \ge\ \frac1n\sum_{i,S}y'_{i,S}\ln v_i(S)-\ln\Bigl(1+\frac1K\Bigr).$$
--
--   This is the configuration LP solver of [FL25, Theorem 2.1], the first step of the algorithm of Theorem 1.1.
--
--   Differences from the source:
--   - reading: "for any $\varepsilon>0$ … running time polynomial in the input size and $1/\varepsilon$" → one machine taking $K=1/\varepsilon$ in unary, polynomial in its input length; reason: implies the printed claim for every $\varepsilon$ (take $K=\lceil1/\varepsilon\rceil$); the per-$\varepsilon$ reading is weaker
--   - reading: "value at least the optimum value of the configuration LP minus $\ln(1+\varepsilon)$" → for every valid $y'$ with finite objective, $y$ has finite objective and value $\ge$ value$(y')-\ln(1+1/K)$; reason: the optimum is the supremum over finite-objective solutions; with none (Remark 2.7) it is $-\infty$ and only validity is claimed
--   - encoding: $n$ agents → $n\ge1$; reason: with no agents and $m\ge1$ goods constraint (3) has no solution
--   - encoding: input valuations in $\mathbb R_{\ge0}$, "polynomial time", "list of the non-zero entries" → rational binary input, `Turing.TM2ComputableInPolyTime` over fixed binary encodings, output a list of entries decoded totally; reason: an algorithm's input and output are finite strings; same instances
-- source:
--   Viswanathan, A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations, arXiv:2607.13340 (held version, sha256 08811cb468c2df39231dca4222c5af94163587c7c83e205e50bbf0b91fc1deb3), Theorem 2.5, p.10; Remark 2.6, p.10

import Mathlib
import Definitions.Def_NSWBetter_Inst
import Definitions.Def_NSWBetter_Inst_WellFormed
import Definitions.Def_NSWBetter_Inst_rv
import Definitions.Def_NSWBetter_IsValidCLP
import Definitions.Def_NSWBetter_FiniteObj
import Definitions.Def_NSWBetter_lpVal
import Definitions.Def_NSWBetter_Entry
import Definitions.Def_NSWBetter_encEntries
import Definitions.Def_NSWBetter_encInstK
import Definitions.Def_NSWBetter_decodeCLP

namespace NSWBetter

/-- **Theorem 2.5 ([FL25]) — approximate configuration LP solver.**
Viswanathan, *A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations*, arXiv:2607.13340 (held version, sha256 08811cb4…), Theorem 2.5, p.10: "For any ε > 0, there is an algorithm that outputs a valid solution {yi,S ∈ Q≥0}i∈N,S⊆G whose value is at least the optimum value of the configuration LP minus ln (1 + ε), represented using a list of the non-zero entries. The running time of the algorithm is polynomial in the input size and 1/ε." (cited from [FL25, Theorem 2.1]; Remark 2.6 for equality in (3)).

There is one Turing machine, polynomial time in the length of `encInstK (I, K)` (the instance in binary and `K` in unary), whose output list of entries decodes to a valid solution `y` of (2)–(4) such that, for every valid solution `y'` with a finite objective, `y` has a finite objective and `lpVal y ≥ lpVal y' − ln(1 + 1/K)`.

**Formalization Note.** `ε = 1/K`: for a given `ε > 0` take `K = ⌈1/ε⌉`; the input length is polynomial in the input size and `1/ε`. The optimum is compared with every finite-objective feasible solution; when none exists (optimal Nash welfare `0`, Remark 2.7) only validity is claimed. `n ≥ 1`: with no agents and `m ≥ 1` goods, (3) has no solution. -/
theorem theorem_2_5 :
    ∃ A : Inst × ℕ → List Entry,
      Nonempty (Turing.TM2ComputableInPolyTime encInstK encEntries A) ∧
      ∀ I : Inst, I.WellFormed → 1 ≤ I.n → ∀ K : ℕ, 1 ≤ K →
        IsValidCLP (decodeCLP I (A (I, K))) ∧
        ∀ y' : Fin I.n → Finset (Fin I.m) → ℝ, IsValidCLP y' → FiniteObj I.rv y' →
          FiniteObj I.rv (decodeCLP I (A (I, K))) ∧
          lpVal I.rv y' - Real.log (1 + 1 / (K : ℝ)) ≤ lpVal I.rv (decodeCLP I (A (I, K))) := by sorry

end NSWBetter
