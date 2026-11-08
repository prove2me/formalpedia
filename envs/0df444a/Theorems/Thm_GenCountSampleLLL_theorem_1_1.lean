-- Prove2me | Theorems.Thm_GenCountSampleLLL_theorem_1_1
-- name    : GenCountSampleLLL.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T04:57:26.30743+00:00
-- url     : https://prove2.me/theorems/2b8326ea-a2a3-4db4-a20e-cbc4aa68a9d8
-- title:
--   Theorem 1.1 with Remark 1.2, p.2 — under (1.1) with $c=1/100$: $Z_{\mathcal C}>0$, an FPRAS for $Z_{\mathcal C}$, and a polynomial expected-time $\varepsilon$-sampler for $\mu_{\mathcal C}$
-- statement:
--   Let $\mathcal C$ be a constraint satisfaction problem on finitely many independent variables with finite domains, and suppose there is $x\in(0,1)^{\mathcal C}$ with
--   $$
--   p_a\le c\,x_a\prod_{b\in N^2_G(a)}(1-x_b)\qquad(a\in\mathcal C),\qquad c=\frac1{100}.\tag{1.1}
--   $$
--   Then:
--   1. $Z_{\mathcal C}>0$;
--   2. there is an FPRAS for $Z_{\mathcal C}$: for every $\varepsilon,\delta$ it outputs a number in $[0,1]$ within relative error $\varepsilon$ of $Z_{\mathcal C}$ with probability at least $1-\delta$, in worst-case time polynomial in the instance size $I$, $1/\varepsilon$ and $\log(1/\delta)$;
--   3. there is a randomized algorithm that, for every $0<\varepsilon\le1$, runs in expected time polynomial in $I$ and $1/\varepsilon$ and returns $\sigma\in\mathrm{Good}(\mathcal C)$ with $\|\mathrm{Law}(\sigma)-\mu_{\mathcal C}\|_{\mathrm{TV}}\le\varepsilon$.
--
--   The algorithms access the instance through its explicit encoding and through oracles for constraint tests and samples from the coordinate laws, as in Remark 1.2, and never read $x$. This is the counting and sampling analogue of the asymmetric Lovász local lemma.
--
--   **Formalization Note** Two admissible programs and constants $C,k$ are fixed before the instance and $x$. The FPRAS reads $E$ and $L$ ($\varepsilon=1/E$, $\delta=2^{-L}$), halts on every branch within log-cost $C(I+E+L+2)^k$, outputs a rational $u/v\in[0,1]$, and has $|\hat Z-Z_{\mathcal C}|\le Z_{\mathcal C}/E$ with probability at least $1-2^{-L}$. The sampler reads $E$ ($\varepsilon=1/E$), halts almost surely, outputs an encoded $\sigma\in\mathrm{Good}(\mathcal C)$, has expected log-cost at most $C(I+E+2)^k$, and its output law is within total variation $1/E$ of $\mu_{\mathcal C}$.
--
--   Differences from the source:
--   - generalization: "There exists a universal constant c > 0" → c = 1/100; reason: Remark 1.2: "For our proof, c = 1/100 is sufficient"; the statement at c = 1/100 implies the existential one
--   - reading: "polynomial time"; "the same basic computational assumptions as in the Moser–Tardos algorithm" (Remark 1.2); no machine is named → programs of the published randomized log-cost oracle RAM `PDSEquiv.Machine` that never use its exact Bernoulli instruction `ber` (`Admissible`); every instruction, query and reply is charged by bit lengths; random bits come from the oracle; reason: a log-cost RAM is polynomially equivalent to a Turing machine, the usual meaning of polynomial time; a unit-cost RAM would be a stronger machine and a weaker theorem
--   - encoding: "oracles for testing constraints and drawing independent samples from the coordinate distributions"; domains, vbl(a) and incidence lists "given explicitly"; instance size I → one oracle `csOracle` answering `[0, v]` (a fresh draw from ν_v), `1 :: a :: vals` (constraint test) and `[2]` (a fair bit); Ω_v relabelled 0, …, q_v − 1; the input `encInst` lists n, m, the q_v, each vbl(a) and each incidence list; `size` is its length plus Σ_v q_v; reason: a fixed concrete encoding of Remark 1.2's input and oracles; the program sees ν, the forbidden sets and x only through the oracle
--   - encoding: real 0 < ε, δ < 1 → ε = 1/E and δ = 2^{−L} for naturals E ≥ 1 and L; reason: E = ⌈1/ε⌉ and L = ⌈log₂(1/δ)⌉ give at least the requested accuracy and confidence at polynomially related cost
--   - generalization: 0 < ε, δ < 1 → also ε = 1 (E = 1) and δ = 1 (L = 0); reason: more inputs; restricting E ≥ 2 and L ≥ 1 gives the source's range
--   - reading: "for every 0 < ε ≤ 1, there is a randomized algorithm" → one sampler program that takes ε as input; reason: Remark 1.2 and Algorithm 4 take ε as an input; the uniform reading is the stronger one
--   - reading: "FPRAS"; "worst-case running time is polynomial"; "estimates Z_C to relative error ε with probability at least 1 − δ" → log-cost bound and halting on every random branch; outputs rationals in [0, 1]; |Ẑ − Z_𝒞| ≤ Z_𝒞/E with probability ≥ 1 − 2^{−L}; reason: Remark 1.2's description; Algorithm 2 outputs a number in [0, 1]
--   - reading: "running in polynomial expected time, which returns σ ∈ Good(𝒞)" → almost-sure halting, every output an encoded σ ∈ Good(𝒞), expected log-cost (non-halting branches charged) bounded; reason: the meaning of an algorithm returning σ ∈ Good(𝒞) in expected polynomial time
-- source:
--   Jain, Mizgerd, Pham, A general counting and sampling Lovász local lemma, arXiv:2609.23671 (held file sha256 cd449f83…), Theorem 1.1 and Remark 1.2, p.2

import Mathlib
import Definitions.Def_GenCountSampleLLL_Inst
import Definitions.Def_PDSEquiv_Machine
import Definitions.Def_GenCountSampleLLL_csOracle
import Definitions.Def_IsingLTL_BeliefProp_TVDist

set_option autoImplicit false

open scoped BigOperators ENNReal

namespace GenCountSampleLLL

open Inst

/-- Theorem 1.1 with Remark 1.2, p.2 (Jain, Mizgerd, Pham, *A general counting and sampling Lovász local lemma*, arXiv:2609.23671 (held file sha256 cd449f83…)).
With `c = 1/100`: suppose `p_a ≤ c x_a ∏_{b ∈ N²_G(a)} (1 − x_b)` for every `a ∈ C` (1.1), for some
`x ∈ (0,1)^C`. Then `Z_C > 0`; there is an FPRAS for `Z_C` (for every `ε, δ`, relative error `ε`
with probability at least `1 − δ`, worst-case time polynomial in `I`, `1/ε`, `log(1/δ)`); and for
every `0 < ε ≤ 1` there is a randomized algorithm, running in polynomial expected time (in `I` and
`1/ε`), which returns `σ ∈ Good(C)` with `‖Law(σ) − µ_C‖_TV ≤ ε`.

**Formalization Note.** Two admissible programs `Pc` (counting) and `Ps` (sampling) and constants
`C, k`, fixed before the instance and `x`, run on the log-cost oracle RAM `PDSEquiv.Machine` with
the CSP oracle `csOracle` (constraint tests, fresh draws from each `ν_v`, fair bits). The FPRAS
reads `encInst ++ [E, L]` (`ε = 1/E`, `δ = 2^{−L}`): on every branch it halts within log-cost
`C (size + E + L + 2)^k`, outputs a rational `[u, v] ∈ [0, 1]`, and
`|Ẑ − Z_C| ≤ Z_C/E` with probability at least `1 − 2^{−L}`. The sampler reads `encInst ++ [E]`
(`ε = 1/E`): it halts almost surely, outputs `encAssign σ` with `σ ∈ Good(C)`, has expected
log-cost at most `C (size + E + 2)^k`, and its output law is within total variation `1/E` of
`µ_C`. The programs never see `x`, `ν`, or the forbidden sets except through the oracle. -/
theorem theorem_1_1 :
    ∃ (Pc Ps : PDSEquiv.Program) (C k : ℕ), Admissible Pc ∧ Admissible Ps ∧
      ∀ (I : Inst) (x : Fin I.m → ℝ), (∀ b, 0 < x b ∧ x b < 1) → I.LLLCond (1 / 100) x →
        0 < I.Z Finset.univ ∧
        (∀ E L : ℕ, 1 ≤ E →
          PDSEquiv.HaltsWithin Pc I.csOracle (I.encInst ++ [E, L])
            (C * (I.size + E + L + 2) ^ k) (C * (I.size + E + L + 2) ^ k) ∧
          PDSEquiv.OutputsSatisfy Pc I.csOracle (I.encInst ++ [E, L]) PDSEquiv.IsRatOut ∧
          1 - (2 : ℝ) ^ (-(L : ℤ)) ≤
            ∑' o, (if |PDSEquiv.ratOut o - I.Z Finset.univ| ≤ I.Z Finset.univ / (E : ℝ) then
              PDSEquiv.outMass Pc I.csOracle (I.encInst ++ [E, L]) o else 0)) ∧
        (∀ E : ℕ, 1 ≤ E →
          HaltsAS Ps I.csOracle (I.encInst ++ [E]) ∧
          PDSEquiv.OutputsSatisfy Ps I.csOracle (I.encInst ++ [E])
            (fun o => ∃ σ ∈ I.Good Finset.univ, o = I.encAssign σ) ∧
          expCost Ps I.csOracle (I.encInst ++ [E]) ≤ ((C * (I.size + E + 2) ^ k : ℕ) : ℝ≥0∞) ∧
          IsingLTL.BeliefProp.tvDist (I.outLaw Ps (I.encInst ++ [E])) (I.mu Finset.univ) ≤
            1 / (E : ℝ)) := by sorry

end GenCountSampleLLL
