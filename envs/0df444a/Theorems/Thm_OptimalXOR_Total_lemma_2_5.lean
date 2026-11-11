-- Prove2me | Theorems.Thm_OptimalXOR_Total_lemma_2_5
-- name    : OptimalXOR.Total.lemma_2_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T16:07:37.159786+00:00
-- url     : https://prove2.me/theorems/f2d7b706-de8a-414a-800d-4ee17490f5b8
-- title:
--   Lemma 2.5 (Independent executions) — (2.16) and (2.17)
-- statement:
--   Throughout, $\mathcal X,\mathcal Y$ are finite nonempty sets, protocols use public and private randomness and output a function of the public randomness and the transcript, and $\mathrm{IC}_\varepsilon(F)$ is the worst-case information complexity (2.9).
--
--   1. Let $\pi_1,\dots,\pi_t$ be protocols on a common input space $\mathcal X\times\mathcal Y$, and let $\pi$ run them with independent randomness, without using the private state or messages of one run in another. Then for every $\mu\in\mathcal P(\mathcal X\times\mathcal Y)$,
--   $$\mathrm{IC}(\pi,\mu)\le\sum_{i=1}^t\mathrm{IC}(\pi_i,\mu).\tag{2.16}$$
--   2. Alternatively, let $\mathcal X=\prod_{i=1}^t\mathcal X_i$, $\mathcal Y=\prod_{i=1}^t\mathcal Y_i$, and let $\pi_i$ run only on the $i$-th coordinate pair $(X_i,Y_i)$ of the input. For an arbitrary $\nu\in\mathcal P(\mathcal X\times\mathcal Y)$, with $\nu_i$ the marginal law of $(X_i,Y_i)$,
--   $$\mathrm{IC}(\pi,\nu)\le\sum_{i=1}^t\mathrm{IC}(\pi_i,\nu_i).\tag{2.17}$$
--   No independence between the coordinates of $\nu$ is assumed.
--
--   Information cost is subadditive over independent runs; this gives the factor-$t$ cost of $t$ repetitions and the upper bound $\mathrm{IC}_{1/3}(F^n)\le n\,\mathrm{IC}_{1/(3n)}(F)$.
--
--   Differences from the source:
--   - encoding: all sets finite and nonempty (standing assumption, p. 12) → [Fintype X] [Nonempty X] [Fintype Y] [Nonempty Y]; reason: the standing assumption made explicit
--   - reading: protocol with public and private randomness, no restriction on the number of rounds (p. 13) → the published CaiZhuInfo.Matrix.Protocol: a finite binary tree with a fixed speaker per node, one bit per message, tapes arbitrary probability spaces, message maps measurable in the tapes; reason: 'no restriction on the number of rounds' read as unbounded but finite; multi-bit messages are sent bit by bit, which preserves transcripts and information
--   - encoding: information quantities of finite random variables → inputs carry the discrete σ-algebra ⊤ inside the definitions; reason: the paper's inputs are finite; conditioning on Y needs the discrete σ-algebra
--   - reading: π runs π₁, …, π_t with independent randomness → indepRun: the runs take place one after the other, each with its own independent public and private tapes and its own messages; reason: the paper's proof uses exactly this, writing the transcript of π as (M₁, …, M_t)
--   - generalization: π and the πᵢ are protocols, so their outputs are functions of public randomness and transcript → no output convention is required of the πᵢ, and the output map of π is an arbitrary measurable map; reason: the information cost does not depend on any output map, so the statement for all outputs specializes to the paper's
--   - encoding: ∏ᵢ Xᵢ, coordinates 1, …, t → dependent functions ∀ i : Fin t, Xs i, coordinates 0, …, t − 1; marginal νᵢ = ν.map (fun p => (p.1 i, p.2 i)); reason: Lean convention
--   - generalization: π₁, …, π_t with t ⩾ 1 → t : ℕ arbitrary; reason: t = 0 adds only the empty protocol (a single leaf, information cost 0 = empty sum); every t ⩾ 1 is the paper's case
-- source:
--   Alexander A. Sherstov, Optimal XOR Lemmas for Information Complexity, STOC 2027 submission (manuscript sha256 91f89aba…), p. 17 (PDF 19), Lemma 2.5, (2.16)–(2.17)

import Mathlib
import Definitions.Def_CaiZhuInfo_Matrix_Protocol
import Definitions.Def_OptimalXOR_Total_Problems
import Definitions.Def_OptimalXOR_Total_InformationComplexity
import Definitions.Def_OptimalXOR_Total_Compositions

open CaiZhuInfo.Matrix
open scoped ENNReal

namespace OptimalXOR.Total

/-- Lemma 2.5 (Independent executions), p. 17. (2.16): if `π` runs `π₁, …, π_t` on a common
input with independent randomness, never using one run's private state or messages in another,
then `IC(π, µ) ≤ ∑ᵢ IC(πᵢ, µ)` for every `µ ∈ P(X × Y)`. (2.17): if `πᵢ` runs only on the `i`-th
coordinate pair of `(X, Y) ∈ ∏ᵢ Xᵢ × ∏ᵢ Yᵢ`, then `IC(π, ν) ≤ ∑ᵢ IC(πᵢ, νᵢ)` for every
`ν ∈ P(X × Y)`, `νᵢ` the marginal law of `(Xᵢ, Yᵢ)`. -/
theorem lemma_2_5 :
    (∀ {X Y Z : Type} [Fintype X] [Nonempty X] [Fintype Y] [Nonempty Y] {t : ℕ}
      {Zs : Fin t → Type} (π : ∀ i, Protocol X Y (Zs i))
      (out : Y → (∀ i, (π i).shared.Carrier) → (∀ i, (π i).privateB.Carrier) → List Bool → Z)
      (hout : ∀ y h, @Measurable ((∀ i, (π i).shared.Carrier) × (∀ i, (π i).privateB.Carrier)) Z
        inferInstance ⊤ (fun u => out y u.1 u.2 h))
      (μ : PMF (X × Y)),
      infoCost (indepRun π (fun _ => id) (fun _ => id) out hout) μ ≤ ∑ i, infoCost (π i) μ) ∧
    (∀ {t : ℕ} {Xs Ys Zs : Fin t → Type} [∀ i, Fintype (Xs i)] [∀ i, Nonempty (Xs i)]
      [∀ i, Fintype (Ys i)] [∀ i, Nonempty (Ys i)] {Z : Type}
      (π : ∀ i, Protocol (Xs i) (Ys i) (Zs i))
      (out : (∀ i, Ys i) → (∀ i, (π i).shared.Carrier) → (∀ i, (π i).privateB.Carrier) →
        List Bool → Z)
      (hout : ∀ y h, @Measurable ((∀ i, (π i).shared.Carrier) × (∀ i, (π i).privateB.Carrier)) Z
        inferInstance ⊤ (fun u => out y u.1 u.2 h))
      (ν : PMF ((∀ i, Xs i) × (∀ i, Ys i))),
      infoCost (indepRun π (fun i x => x i) (fun i y => y i) out hout) ν ≤
        ∑ i, infoCost (π i) (ν.map fun p => (p.1 i, p.2 i))) := by sorry

end OptimalXOR.Total
