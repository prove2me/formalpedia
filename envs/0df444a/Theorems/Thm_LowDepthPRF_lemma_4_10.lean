-- Prove2me | Theorems.Thm_LowDepthPRF_lemma_4_10
-- name    : LowDepthPRF.lemma_4_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:39:43.941882+00:00
-- url     : https://prove2.me/theorems/77c8532d-a453-489c-825f-e5e176ca1063
-- title:
--   Lemma 4.10 — the statistical step $\mathbf H_{1,m,c_q}\approx_{q,\infty,2^{-m}}\mathbf H_2$
-- statement:
--   Let $\mathscr G$ be key-uniform, let $H_\lambda$ be a 2-wise independent hashing, and let $q,\lambda$ satisfy $c_q=\lceil2\log_\Delta q\rceil<\ell$, with $m=\lambda$. Then the game $\mathbf H_{1,m,c_q}$, which gives oracle access to a random member of $\mathscr F'_{(m,c_q)}=\mathscr F_{(c_q)}^{\oplus m}$, and the game $\mathbf H_2$, which gives oracle access to a uniformly random function, are
--
--   $$(q,\infty,2^{-m})\text{-indistinguishable}.$$
--
--   The bound holds against adversaries of every size, so after the first $c_q$ levels no computational assumption is needed.
--
--   Differences from the source:
--   - reading: the setting of Theorem 4.6's proof (𝒢 key-uniform, H 2-wise independent, c_q < ℓ) → these as explicit hypotheses, with H 2-wise independent at the λ considered; reason: the lemma uses exactly these
--   - encoding: TGGM_(c_q) at c_q = 0 → R on the empty prefix as the root key; reason: the paper's own reading in the proof
--   - encoding: 2^{−m} → 1/2^λ; reason: m = λ
--   - encoding: circuits with bounded fan-in {AND, OR, NOT} gates and oracle gates, size, depth → well-formed straight-line circuits; size = number of non-input gates with an oracle gate counting 1; depth counted in gates with inputs and constants at depth 0; query count = number of oracle gates; reason: the paper fixes only the gate basis; these are the standard conventions, under which Lemma 3.12 is lossless
--   - encoding: probabilities over uniform choices of keys, inputs and functions → uniform averages over finite types (uprob); reason: every experiment of the paper samples uniformly from finite sets
-- source:
--   Ding, Jain, Komargodski, Pseudorandom Functions in NC¹ from LWE/LPN/CDH, arXiv:2608.25213 (sha256 89a55849…), Lemma 4.10, p.21 (pdf 23), in the proof of Theorem 4.6

import Mathlib
import Definitions.Def_LowDepthPRF_HybridFamily

namespace LowDepthPRF

/-- **Lemma 4.10** (Ding, Jain, Komargodski, arXiv:2608.25213, sha256 89a55849…, p.21). In the
proof of Theorem 4.6 (fix `q` and `λ` with `c_q < ℓ`): games `H_{1,m,c_q}` and `H_2` are
`(q, ∞, 2^{−m})`-indistinguishable.

**Formalization Note.** Self-contained form with the hypotheses of the setting: `𝒢` is
key-uniform (every `G_n` is 1-wise independent, Definition 4.1) and `H_λ` is a 2-wise independent
hashing (on its `ℓ · log Δ` output bits, equivalently on `[Δ]^ℓ`). `m = λ`; `H_{1,m,c_q}` is the
strong real game of `ℱ′_{(m,c_q)}` and `H_2` gives a uniformly random function
`{0,1}^λ → {0,1}^{λ^{(ℓ+1)}}`. Adversaries of every size, making at most `q` (possibly adaptive,
possibly repeated) queries. -/
theorem lemma_4_10 (p : ℕ → ℕ) (G : (n : ℕ) → FunFam (Fin n → Bool) (p n) (ceilSqrt n))
    (hGku : ∀ n, NWiseIndep (G n) 1) (kh : ℕ → ℕ)
    (H : (lam : ℕ) → FunFam (Fin (kh lam) → Bool) lam (ell lam * logDelta lam))
    (q lam : ℕ) (hH : NWiseIndep (H lam) 2) (hq : cq q lam < ell lam) :
    IndistAll (strongReal (hybridFam G H q lam lam (cq q lam)))
      (strongIdeal lam (tl lam (ell lam))) q (1 / (2 : ℝ) ^ lam) := by sorry

end LowDepthPRF
