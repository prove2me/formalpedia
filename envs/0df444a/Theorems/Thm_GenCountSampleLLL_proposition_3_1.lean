-- Prove2me | Theorems.Thm_GenCountSampleLLL_proposition_3_1
-- name    : GenCountSampleLLL.proposition_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T04:56:16.03687+00:00
-- url     : https://prove2.me/theorems/2fad4258-21ca-4854-9cee-1c5355d877d8
-- title:
--   Proposition 3.1, p.11 — an unbiased estimator of $r_{\mathcal D,a}$ with $\mathbb E\hat r^2_{\mathcal D,a}\le3cx_a$ in polynomial expected time
-- statement:
--   Assume (1.1) with $c=1/100$ for some $x\in(0,1)^{\mathcal C}$. For every $a\in\mathcal D\subseteq\mathcal C$ there is an estimator $\hat r_{\mathcal D,a}$ with
--   $$
--   \mathbb E\,\hat r_{\mathcal D,a}=r_{\mathcal D,a},\qquad\mathbb E\,\hat r^2_{\mathcal D,a}\le3c\,x_a,
--   $$
--   and the expected running time to generate it is polynomial in the instance size $I$. Concretely:
--   1. one admissible program, with constants $C,k$ chosen before the instance, given the encoded instance, $\mathcal D$ and $a$ and the CSP oracle, halts almost surely with an integer output whose law has finite first and second moments, mean $r_{\mathcal D,a}$ and second moment at most $3cx_a$, at expected cost at most $C(I+2)^k$;
--   2. Algorithm 1's output $\hat r_{\mathcal D,a}$ has the same mean and second-moment properties.
--
--   Averaging copies of the estimator approximates each factor of $Z_{\mathcal C}=\prod_i(1-r_{\mathcal C_i,a_i})$.
--
--   Differences from the source:
--   - encoding: the standing assumption of §2, p.7: "Throughout the proof, we assume (1.1) with c = 1/100", with x ∈ (0,1)^𝒞 → explicit hypotheses `hx : ∀ b, 0 < x b ∧ x b < 1` and `hLLL : I.LLLCond (1/100) x`; reason: the statement on the page omits the section's standing assumption; the Lean states it
--   - reading: "polynomial time"; "the same basic computational assumptions as in the Moser–Tardos algorithm" (Remark 1.2); no machine is named → programs of the published randomized log-cost oracle RAM `PDSEquiv.Machine` that never use its exact Bernoulli instruction `ber` (`Admissible`); every instruction, query and reply is charged by bit lengths; random bits come from the oracle; reason: a log-cost RAM is polynomially equivalent to a Turing machine, the usual meaning of polynomial time; a unit-cost RAM would be a stronger machine and a weaker theorem
--   - encoding: "oracles for testing constraints and drawing independent samples from the coordinate distributions"; domains, vbl(a) and incidence lists "given explicitly"; instance size I → one oracle `csOracle` answering `[0, v]` (a fresh draw from ν_v), `1 :: a :: vals` (constraint test) and `[2]` (a fair bit); Ω_v relabelled 0, …, q_v − 1; the input `encInst` lists n, m, the q_v, each vbl(a) and each incidence list; `size` is its length plus Σ_v q_v; reason: a fixed concrete encoding of Remark 1.2's input and oracles; the program sees ν, the forbidden sets and x only through the oracle
--   - reading: "there is an estimator" for every a ∈ 𝒟 ⊆ 𝒞 with polynomial expected running time → one program for all instances, 𝒟 and a, with C and k fixed first, and in addition the same moment statements for Algorithm 1's law; reason: a uniform program is the stronger reading; the paper's estimator is Algorithm 1
--   - encoding: 𝔼r̂, 𝔼r̂² of a real estimator → integer outputs [0, k] ↦ k, [1, k] ↦ −k; summability of |r̂| and r̂² against the output law stated; reason: r̂ is an integer (built from 0, 1, signs and 4Y); `outExpect` is a sum that is 0 when not summable
-- source:
--   Jain, Mizgerd, Pham, A general counting and sampling Lovász local lemma, arXiv:2609.23671 (held file sha256 cd449f83…), Proposition 3.1, p.11, with Algorithm 1, p.12

import Mathlib
import Definitions.Def_GenCountSampleLLL_Inst
import Definitions.Def_GenCountSampleLLL_twoTrees
import Definitions.Def_GenCountSampleLLL_estLaw
import Definitions.Def_PDSEquiv_Machine
import Definitions.Def_GenCountSampleLLL_csOracle

set_option autoImplicit false

open scoped BigOperators ENNReal

namespace GenCountSampleLLL

open Inst

/-- Proposition 3.1, p.11 (Jain, Mizgerd, Pham, *A general counting and sampling Lovász local lemma*, arXiv:2609.23671 (held file sha256 cd449f83…)), under (1.1) with `c = 1/100`.
For every `a ∈ D ⊆ C` there is an estimator `r̂_{D,a}` with `E r̂_{D,a} = r_{D,a}` and
`E r̂²_{D,a} ≤ 3c x_a`, whose expected running time is polynomial in `I`.

**Formalization Note.** Two readings of "there is an estimator", both asserted. (1) One admissible
program on the log-cost oracle RAM `PDSEquiv.Machine`, with constants `C, k` fixed before the
instance, which on input `encInst ++ encFamily D ++ [a]` and with the CSP oracle halts almost
surely with an integer output (`[0, k]` is `k`, `[1, k]` is `−k`), whose output law has finite
first and second moments, mean `r_{D,a}` and second moment at most `3c x_a`, at expected log-cost
at most `C (size + 2)^k`. The program never reads `x`. (2) Algorithm 1 itself (`estLaw`) has
these mean and second-moment properties. -/
theorem proposition_3_1 :
    ∃ (P : PDSEquiv.Program) (C k : ℕ), Admissible P ∧
      ∀ (I : Inst) (x : Fin I.m → ℝ), (∀ b, 0 < x b ∧ x b < 1) → I.LLLCond (1 / 100) x →
      ∀ (D : Finset (Fin I.m)) (a : Fin I.m), a ∈ D →
        (HaltsAS P I.csOracle (I.encInst ++ I.encFamily D ++ [(a : ℕ)]) ∧
          PDSEquiv.OutputsSatisfy P I.csOracle (I.encInst ++ I.encFamily D ++ [(a : ℕ)])
            IsIntOut ∧
          Summable (fun o => PDSEquiv.outMass P I.csOracle
            (I.encInst ++ I.encFamily D ++ [(a : ℕ)]) o * |intOut o|) ∧
          Summable (fun o => PDSEquiv.outMass P I.csOracle
            (I.encInst ++ I.encFamily D ++ [(a : ℕ)]) o * intOut o ^ 2) ∧
          PDSEquiv.outExpect P I.csOracle (I.encInst ++ I.encFamily D ++ [(a : ℕ)]) intOut =
            I.r D a ∧
          PDSEquiv.outExpect P I.csOracle (I.encInst ++ I.encFamily D ++ [(a : ℕ)])
            (fun o => intOut o ^ 2) ≤ 3 * (1 / 100) * x a ∧
          expCost P I.csOracle (I.encInst ++ I.encFamily D ++ [(a : ℕ)]) ≤
            ((C * (I.size + 2) ^ k : ℕ) : ℝ≥0∞)) ∧
        (Summable (fun vn : ℤ × ℕ => (I.estLaw D a vn).toReal * |(vn.1 : ℝ)|) ∧
          Summable (fun vn : ℤ × ℕ => (I.estLaw D a vn).toReal * (vn.1 : ℝ) ^ 2) ∧
          ∑' vn : ℤ × ℕ, (I.estLaw D a vn).toReal * (vn.1 : ℝ) = I.r D a ∧
          ∑' vn : ℤ × ℕ, (I.estLaw D a vn).toReal * (vn.1 : ℝ) ^ 2 ≤
            3 * (1 / 100) * x a) := by sorry

end GenCountSampleLLL
