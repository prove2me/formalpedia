-- Prove2me | Theorems.Thm_GenCountSampleLLL_proposition_2_2
-- name    : GenCountSampleLLL.proposition_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T04:57:24.861532+00:00
-- url     : https://prove2.me/theorems/d69c3625-224a-4825-9adb-dd066a5c18e1
-- title:
--   Proposition 2.2, p.8 — the insertion map: polynomial expected time, $\|\mathrm{Law}(\tau)-\mu_{\mathcal D}\|_{\mathrm{TV}}\le\delta$
-- statement:
--   Assume (1.1) with $c=1/100$ for some $x\in(0,1)^{\mathcal C}$. For every $a\in\mathcal D\subseteq\mathcal C$ and $0<\delta\le1$ there is a randomized map $\mathrm{Insert}(\mathcal D,a,\cdot,\delta)$ from $\mathrm{Good}(\mathcal D^-)$ to $\mathrm{Good}(\mathcal D)$, with expected running time polynomial in $I$ and $1/\delta$, such that if $\sigma\sim\mu_{\mathcal D^-}$ and $\tau=\mathrm{Insert}(\mathcal D,a,\sigma,\delta)$, then
--   $$
--   \|\mathrm{Law}(\tau)-\mu_{\mathcal D}\|_{\mathrm{TV}}\le\delta.
--   $$
--   Concretely, one admissible program with constants $C,k$ fixed first, given the encoded instance, $\mathcal D$, $a$, $\sigma$ and $E$ (with $\delta=1/E$), for every $\sigma\in\mathrm{Good}(\mathcal D^-)$ halts almost surely, outputs some $\tau\in\mathrm{Good}(\mathcal D)$, and has expected cost at most $C(I+E+2)^k$; the output law averaged over $\sigma\sim\mu_{\mathcal D^-}$ is within total variation $1/E$ of $\mu_{\mathcal D}$.
--
--   Inserting $a_1,\dots,a_m$ in turn with $\delta=\varepsilon/(m+1)$ gives the sampler of Theorem 1.1.
--
--   Differences from the source:
--   - encoding: the standing assumption of §2, p.7: "Throughout the proof, we assume (1.1) with c = 1/100", with x ∈ (0,1)^𝒞 → explicit hypotheses `hx : ∀ b, 0 < x b ∧ x b < 1` and `hLLL : I.LLLCond (1/100) x`; reason: the statement on the page omits the section's standing assumption; the Lean states it
--   - reading: "polynomial time"; "the same basic computational assumptions as in the Moser–Tardos algorithm" (Remark 1.2); no machine is named → programs of the published randomized log-cost oracle RAM `PDSEquiv.Machine` that never use its exact Bernoulli instruction `ber` (`Admissible`); every instruction, query and reply is charged by bit lengths; random bits come from the oracle; reason: a log-cost RAM is polynomially equivalent to a Turing machine, the usual meaning of polynomial time; a unit-cost RAM would be a stronger machine and a weaker theorem
--   - encoding: "oracles for testing constraints and drawing independent samples from the coordinate distributions"; domains, vbl(a) and incidence lists "given explicitly"; instance size I → one oracle `csOracle` answering `[0, v]` (a fresh draw from ν_v), `1 :: a :: vals` (constraint test) and `[2]` (a fair bit); Ω_v relabelled 0, …, q_v − 1; the input `encInst` lists n, m, the q_v, each vbl(a) and each incidence list; `size` is its length plus Σ_v q_v; reason: a fixed concrete encoding of Remark 1.2's input and oracles; the program sees ν, the forbidden sets and x only through the oracle
--   - encoding: real 0 < δ ≤ 1 → δ = 1/E for a natural number E ≥ 1; reason: E = ⌈1/δ⌉ gives accuracy at least δ at polynomially related cost
--   - reading: "there is a randomized map Insert(𝒟, a, ·, δ)" for every 𝒟, a, δ, "with expected running time polynomial" → one program for all instances, 𝒟, a and E, with C and k fixed first; for every input σ ∈ Good(𝒟⁻): almost-sure halting, output in Good(𝒟), expected cost bound; reason: the uniform, per-input reading is the stronger one
--   - reading: Algorithm 5 takes a fallback σ⋆ ∈ Good(𝒞) as an extra input → the input carries no fallback assignment; reason: the printed statement has none; the program can compute one itself (Moser–Tardos, p.31)
-- source:
--   Jain, Mizgerd, Pham, A general counting and sampling Lovász local lemma, arXiv:2609.23671 (held file sha256 cd449f83…), Proposition 2.2, p.8 (proved in §7, pp.29–31)

import Mathlib
import Definitions.Def_GenCountSampleLLL_Inst
import Definitions.Def_PDSEquiv_Machine
import Definitions.Def_GenCountSampleLLL_csOracle
import Definitions.Def_IsingLTL_BeliefProp_TVDist

set_option autoImplicit false

open scoped BigOperators ENNReal

namespace GenCountSampleLLL

open Inst

/-- Proposition 2.2, p.8 (Jain, Mizgerd, Pham, *A general counting and sampling Lovász local lemma*, arXiv:2609.23671 (held file sha256 cd449f83…)), under (1.1) with `c = 1/100`.
For every `a ∈ D ⊆ C` and `0 < δ ≤ 1` there is a randomized map `Insert(D, a, ·, δ)` from
`Good(D⁻)` to `Good(D)`, with expected running time polynomial in `I` and `1/δ`, such that if
`σ ∼ µ_{D⁻}` and `τ = Insert(D, a, σ, δ)`, then `‖Law(τ) − µ_D‖_TV ≤ δ`.

**Formalization Note.** One admissible program for all instances, `D`, `a` and `δ = 1/E`
(`E ≥ 1`), with `C, k` fixed first, on the log-cost oracle RAM `PDSEquiv.Machine` with the CSP
oracle. Its input is `encInst ++ encFamily D ++ [a] ++ encAssign σ ++ [E]`. For every
`σ ∈ Good(D⁻)` it halts almost surely, every output is `encAssign τ` with `τ ∈ Good(D)`, and its
expected log-cost is at most `C (size + E + 2)^k`. The output law averaged over `σ ∼ µ_{D⁻}` is
within total variation `1/E` of `µ_D`. The input carries no fallback assignment. -/
theorem proposition_2_2 :
    ∃ (P : PDSEquiv.Program) (C k : ℕ), Admissible P ∧
      ∀ (I : Inst) (x : Fin I.m → ℝ), (∀ b, 0 < x b ∧ x b < 1) → I.LLLCond (1 / 100) x →
      ∀ (D : Finset (Fin I.m)) (a : Fin I.m), a ∈ D → ∀ E : ℕ, 1 ≤ E →
        (∀ σ ∈ I.Good (D.erase a),
          HaltsAS P I.csOracle (I.encInst ++ I.encFamily D ++ [(a : ℕ)] ++ I.encAssign σ ++ [E]) ∧
          PDSEquiv.OutputsSatisfy P I.csOracle (I.encInst ++ I.encFamily D ++ [(a : ℕ)] ++ I.encAssign σ ++ [E])
            (fun o => ∃ τ ∈ I.Good D, o = I.encAssign τ) ∧
          expCost P I.csOracle (I.encInst ++ I.encFamily D ++ [(a : ℕ)] ++ I.encAssign σ ++ [E]) ≤
            ((C * (I.size + E + 2) ^ k : ℕ) : ℝ≥0∞)) ∧
        IsingLTL.BeliefProp.tvDist
          (fun τ => ∑ σ ∈ I.Good (D.erase a),
            I.mu (D.erase a) σ * I.outLaw P (I.encInst ++ I.encFamily D ++ [(a : ℕ)] ++ I.encAssign σ ++ [E]) τ)
          (I.mu D) ≤ 1 / (E : ℝ) := by sorry

end GenCountSampleLLL
