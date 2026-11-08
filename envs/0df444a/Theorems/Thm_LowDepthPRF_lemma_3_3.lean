-- Prove2me | Theorems.Thm_LowDepthPRF_lemma_3_3
-- name    : LowDepthPRF.lemma_3_3
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T06:35:24.034892+00:00
-- url     : https://prove2.me/theorems/dcc30478-26a7-443c-8013-b9b1edbb7502
-- title:
--   Lemma 3.3 — triangle inequality for $(q,t,\epsilon)$-indistinguishability
-- statement:
--   Let $\mathbf H_0,\mathbf H_1,\mathbf H_2$ be games with the same interface. If $\mathbf H_0,\mathbf H_1$ are $(q_1,t_1,\epsilon_1)$-indistinguishable and $\mathbf H_1,\mathbf H_2$ are $(q_2,t_2,\epsilon_2)$-indistinguishable, then
--
--   $$\mathbf H_0\approx_{\min\{q_1,q_2\},\ \min\{t_1,t_2\},\ \epsilon_1+\epsilon_2}\mathbf H_2 .$$
--
--   This is how the hybrid arguments of the paper add up their losses.
--
--   Differences from the source:
--   - generalization: q, t ∈ ℕ and ε > 0 → t₁, t₂ real and ε₁, ε₂ arbitrary reals; reason: for natural sizes and positive ε this is the printed statement
--   - encoding: circuits with bounded fan-in {AND, OR, NOT} gates and oracle gates, size, depth → well-formed straight-line circuits; size = number of non-input gates with an oracle gate counting 1; depth counted in gates with inputs and constants at depth 0; query count = number of oracle gates; reason: the paper fixes only the gate basis; these are the standard conventions, under which Lemma 3.12 is lossless
--   - encoding: probabilities over uniform choices of keys, inputs and functions → uniform averages over finite types (uprob); reason: every experiment of the paper samples uniformly from finite sets
-- source:
--   Ding, Jain, Komargodski, Pseudorandom Functions in NC¹ from LWE/LPN/CDH, arXiv:2608.25213 (sha256 89a55849…), Lemma 3.3, p.11 (pdf 13)

import Mathlib
import Definitions.Def_LowDepthPRF_Game

namespace LowDepthPRF

/-- **Lemma 3.3 (Triangle Inequality)** (Ding, Jain, Komargodski, arXiv:2608.25213, sha256
89a55849…, p.11). If `H₀, H₁` are `(q₁, t₁, ε₁)`-indistinguishable and `H₁, H₂` are
`(q₂, t₂, ε₂)`-indistinguishable, then `H₀, H₂` are `(min{q₁,q₂}, min{t₁,t₂}, ε₁+ε₂)`-
indistinguishable.

**Formalization Note.** The three games present the same interface (sample length `n`, oracle
arities `oa`, `ob`), as hybrids do. Sizes `t₁, t₂` are real numbers and `ε₁, ε₂` are not required
to be positive; for `q, t ∈ ℕ` and `ε > 0` this is the printed statement. -/
theorem lemma_3_3 {n oa ob : ℕ} (H₀ H₁ H₂ : Game n oa ob) (q₁ q₂ : ℕ) (t₁ t₂ ε₁ ε₂ : ℝ)
    (h₀₁ : Indist H₀ H₁ q₁ t₁ ε₁) (h₁₂ : Indist H₁ H₂ q₂ t₂ ε₂) :
    Indist H₀ H₂ (min q₁ q₂) (min t₁ t₂) (ε₁ + ε₂) := by sorry

end LowDepthPRF
