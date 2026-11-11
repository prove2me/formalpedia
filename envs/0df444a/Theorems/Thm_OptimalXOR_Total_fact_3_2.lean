-- Prove2me | Theorems.Thm_OptimalXOR_Total_fact_3_2
-- name    : OptimalXOR.Total.fact_3_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T16:08:16.89013+00:00
-- url     : https://prove2.me/theorems/ca64ad2c-6e84-4519-a5f3-3dc9e18e283f
-- title:
--   Fact 3.2 — $\sum_{j=1}^t\mathrm{IC}(\pi^{(j)},\nu)=\mathrm{IC}(\pi,\nu^t)$
-- statement:
--   Throughout, $\mathcal X,\mathcal Y$ are finite nonempty sets, protocols use public and private randomness and output a function of the public randomness and the transcript, and $\mathrm{IC}_\varepsilon(F)$ is the worst-case information complexity (2.9).
--
--   Let $D\subseteq\mathcal X\times\mathcal Y$, let $\nu\in\mathcal P(D)$, and let $t\ge1$ be an integer. For every protocol $\pi$ with input in $\mathcal X^t\times\mathcal Y^t$, the standard embeddings $\pi^{(1)},\dots,\pi^{(t)}$ into $\pi$ with respect to $\nu$ (Definition 3.1) satisfy
--   $$\sum_{j=1}^t\mathrm{IC}(\pi^{(j)},\nu)=\mathrm{IC}(\pi,\nu^t).\tag{3.1}$$
--
--   The information cost of a protocol under a product distribution splits exactly among its single-coordinate embeddings; this is the folklore identity behind every direct-sum argument for information.
--
--   Differences from the source:
--   - encoding: all sets finite and nonempty (standing assumption, p. 12) → [Fintype X] [Nonempty X] [Fintype Y] [Nonempty Y]; reason: the standing assumption made explicit
--   - reading: protocol with public and private randomness, no restriction on the number of rounds (p. 13) → the published CaiZhuInfo.Matrix.Protocol: a finite binary tree with a fixed speaker per node, one bit per message, tapes arbitrary probability spaces, message maps measurable in the tapes; reason: 'no restriction on the number of rounds' read as unbounded but finite; multi-bit messages are sent bit by bit, which preserves transcripts and information
--   - encoding: information quantities of finite random variables → inputs carry the discrete σ-algebra ⊤ inside the definitions; reason: the paper's inputs are finite; conditioning on Y needs the discrete σ-algebra
--   - encoding: Xⁿ, coordinates 1, …, n → Fin n → X, coordinates 0, …, n−1; reason: Lean convention
--   - encoding: D ⊆ X × Y and ν ∈ P(D) → ν : PMF (X × Y), D omitted; reason: every ν lies in P(D) for D = supp ν, and the embedding depends only on ν
--   - generalization: π a protocol (output a function of public randomness and transcript) → π any protocol with any output type Z, no output convention required; reason: information cost does not depend on the output map; the paper's case is included
--   - encoding: private sampling from conditional laws under νᵗ (Definition 3.1) → standardEmbedding: table-based private sampling, conditional law on a null event = the marginal; reason: same joint law of input, public randomness and transcript; the paper lets null conditionals be arbitrary
-- source:
--   Alexander A. Sherstov, Optimal XOR Lemmas for Information Complexity, STOC 2027 submission (manuscript sha256 91f89aba…), p. 22 (PDF 24), Fact 3.2, (3.1)

import Mathlib
import Definitions.Def_CaiZhuInfo_Matrix_Protocol
import Definitions.Def_OptimalXOR_Total_Problems
import Definitions.Def_OptimalXOR_Total_InformationComplexity
import Definitions.Def_OptimalXOR_Total_Compositions
import Definitions.Def_OptimalXOR_Total_StandardEmbedding

open CaiZhuInfo.Matrix
open scoped ENNReal

namespace OptimalXOR.Total

/-- Fact 3.2 (Information cost of the standard embeddings), p. 22. For `ν ∈ P(X × Y)`, an
integer `t ≥ 1` and every protocol `π` with input in `Xᵗ × Yᵗ`, the standard embeddings
`π^{(1)}, …, π^{(t)}` into `π` with respect to `ν` satisfy `∑ⱼ IC(π^{(j)}, ν) = IC(π, νᵗ)` (3.1). -/
theorem fact_3_2 {X Y Z : Type} [Fintype X] [Nonempty X] [Fintype Y] [Nonempty Y]
    (ν : PMF (X × Y)) (t : ℕ) (ht : 1 ≤ t) (π : Protocol (Fin t → X) (Fin t → Y) Z) :
    ∑ j : Fin t, infoCost (standardEmbedding ν π j) ν = infoCost π (pmfPow ν t) := by sorry

end OptimalXOR.Total
