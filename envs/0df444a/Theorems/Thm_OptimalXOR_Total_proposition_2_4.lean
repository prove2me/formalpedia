-- Prove2me | Theorems.Thm_OptimalXOR_Total_proposition_2_4
-- name    : OptimalXOR.Total.proposition_2_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T16:07:18.55399+00:00
-- url     : https://prove2.me/theorems/38cb2def-bbab-48ce-a8b5-552c2169bb5c
-- title:
--   Proposition 2.4 (Conditional composition) — $\mathrm{IC}(\pi',\mu)\le\mathrm{IC}(\pi,\mu)+qK$ and the error bound
-- statement:
--   Throughout, $\mathcal X,\mathcal Y$ are finite nonempty sets, protocols use public and private randomness and output a function of the public randomness and the transcript, and $\mathrm{IC}_\varepsilon(F)$ is the worst-case information complexity (2.9).
--
--   Let $F:\mathcal X\times\mathcal Y\to\mathcal Z\cup\{*\}$ be a communication problem, let $\pi$ and $\rho$ be protocols with input space $\mathcal X\times\mathcal Y$ and output space $\mathcal Z$, and let $\mathcal M$ be a set of transcripts of $\pi$. Let $\pi'$ run $\pi$ and then, if the transcript of $\pi$ lies in $\mathcal M$, run $\rho$ on the same input with fresh public and private randomness; its output is that of $\rho$ if $\rho$ is run and that of $\pi$ otherwise. Suppose that $\mathrm{IC}(\rho,\nu)\le K$ for every $\nu\in\mathcal P(\operatorname{dom}F)$ and $\mathrm{err}(\rho,F)\le\varepsilon$. Then for every $\mu\in\mathcal P(\operatorname{dom}F)$,
--   $$\mathrm{IC}(\pi',\mu)\le\mathrm{IC}(\pi,\mu)+qK,\qquad \mathrm{err}_\mu(\pi',F)\le\mathbf P[M\notin\mathcal M,\ \pi(X,Y)\neq F(X,Y)]+q\varepsilon,$$
--   where $(X,Y)\sim\mu$, $M$ is the transcript of $\pi$ on input $(X,Y)$, and $q=\mathbf P[M\in\mathcal M]$.
--
--   This is the tool that lets a fallback protocol be run only on some transcripts while its cost is charged only with the probability of those transcripts.
--
--   Differences from the source:
--   - encoding: F : X × Y → Z ∪ {∗} with nonempty dom F → F : X → Y → Option Z (none = ∗) with the hypothesis (dom F).Nonempty; reason: Lean convention; the same problems, and the paper requires dom F ≠ ∅ (p. 12)
--   - encoding: all sets finite and nonempty (standing assumption, p. 12) → [Fintype X] [Nonempty X] [Fintype Y] [Nonempty Y]; reason: the standing assumption made explicit
--   - reading: protocol with public and private randomness, no restriction on the number of rounds (p. 13) → the published CaiZhuInfo.Matrix.Protocol: a finite binary tree with a fixed speaker per node, one bit per message, tapes arbitrary probability spaces, message maps measurable in the tapes; reason: 'no restriction on the number of rounds' read as unbounded but finite; multi-bit messages are sent bit by bit, which preserves transcripts and information
--   - encoding: the output is a function of the public randomness and the transcript (p. 13) → Protocol.TranscriptDetermined: for every input, Bob's output equals almost surely a measurable function of (public tape, message history); imposed on every protocol in IC_ε, IC_ε(F, µ) and on every protocol the statement quantifies over; reason: the published form of the paper's output convention
--   - encoding: information complexities are nonnegative reals (infimum over protocols, supremum over P(dom F)) → values in ℝ≥0∞: IC(π, µ) enters as ENNReal.ofReal of the published real information cost; inf ∅ = ∞; errors are reals; reason: no junk values for sup/inf; same numbers whenever the paper's quantities are defined
--   - encoding: information quantities of finite random variables → inputs carry the discrete σ-algebra ⊤ inside the definitions; reason: the paper's inputs are finite; conditioning on Y needs the discrete σ-algebra
--   - encoding: output set Z → [Fintype Z] [Nonempty Z]; reason: standing assumption that all sets are finite and nonempty
--   - encoding: π′ runs ρ after π only on transcripts in ℳ, with fresh randomness → condCompose π ρ ℳ: ρ's tree grafted at exactly the leaves of π's tree whose message history lies in ℳ; public and private tapes are products of those of π and ρ; reason: the fixed-tree form of the same protocol
--   - encoding: transcripts M of π; q = P[M ∈ ℳ] → ℳ : Set (List Bool) of message histories; probabilities are execProb π μ of the events {history ∈ ℳ} and {history ∉ ℳ ∧ π errs}; reason: Lean convention
-- source:
--   Alexander A. Sherstov, Optimal XOR Lemmas for Information Complexity, STOC 2027 submission (manuscript sha256 91f89aba…), pp. 16–17 (PDF 18–19), Proposition 2.4

import Mathlib
import Definitions.Def_CaiZhuInfo_Matrix_Protocol
import Definitions.Def_OptimalXOR_Total_Problems
import Definitions.Def_OptimalXOR_Total_InformationComplexity
import Definitions.Def_OptimalXOR_Total_Compositions

open CaiZhuInfo.Matrix
open scoped ENNReal

namespace OptimalXOR.Total

/-- Proposition 2.4 (Conditional composition), pp. 16–17. Let `π′` run `π` and then, if the
transcript `M` of `π` lies in `ℳ`, run `ρ` on the same input with fresh randomness (output `ρ`'s
answer if `ρ` is run, `π`'s otherwise). If `IC(ρ, ν) ≤ K` for every `ν ∈ P(dom F)` and
`err(ρ, F) ≤ ε`, then for every `µ ∈ P(dom F)`, with `q = P[M ∈ ℳ]`:
`IC(π′, µ) ≤ IC(π, µ) + qK` and `err_µ(π′, F) ≤ P[M ∉ ℳ, π(X, Y) ≠ F(X, Y)] + qε`. -/
theorem proposition_2_4 {X Y Z : Type} [Fintype X] [Nonempty X] [Fintype Y] [Nonempty Y]
    [Fintype Z] [Nonempty Z] (F : X → Y → Option Z) (hF : (dom F).Nonempty)
    (π ρ : Protocol X Y Z) (hπ : π.TranscriptDetermined) (hρ : ρ.TranscriptDetermined)
    (ℳ : Set (List Bool)) (K ε : ℝ)
    (hK : ∀ ν ∈ Distributions F, infoCost ρ ν ≤ K) (hε : worstError ρ F ≤ ε)
    (μ : PMF (X × Y)) (hμ : μ ∈ Distributions F) :
    infoCost (condCompose π ρ ℳ) μ ≤
        infoCost π μ + execProb π μ {ω | π.history ω.1.1 ω.1.2 ω.2 ∈ ℳ} * K ∧
      distError (condCompose π ρ ℳ) μ F ≤
        execProb π μ {ω | π.history ω.1.1 ω.1.2 ω.2 ∉ ℳ ∧
            some (π.output ω.1.1 ω.1.2 ω.2) ≠ F ω.1.1 ω.1.2} +
          execProb π μ {ω | π.history ω.1.1 ω.1.2 ω.2 ∈ ℳ} * ε := by sorry

end OptimalXOR.Total
