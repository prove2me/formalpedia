-- Prove2me | Theorems.Thm_MixedORAM_PublicRead_lemma_A_2
-- name    : MixedORAM.PublicRead.lemma_A_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T00:46:13.560201+00:00
-- url     : https://prove2.me/theorems/984e3e81-0b2a-434c-927d-35090cf00253
-- title:
--   Lemma A.2 — a message sent before the queried coordinate: s ≤ β/(kw) + 1/w
-- statement:
--   Let $k\ge1$ and $w\ge1$. Let $X_1,\dots,X_k$ be independent uniform $w$-bit words, independent of side information $Z$, which has an arbitrary law. An encoder sends a fixed-length $\beta$-bit message $V=\mathrm{enc}(X,Z)$ before an independent uniform $J\in\{1,\dots,k\}$ is supplied, and a decoder given $V$, $Z$ and $J$ outputs a guess of $X_J$. If $s$ is the probability that the guess equals $X_J$, then
--   $$s\ \le\ \frac{\beta}{kw}+\frac1w .$$
--   Consequently, if $\beta\le kw/16$ and $w\ge4$, then $s\le 5/16$.
--
--   This is the information step of the per-epoch edge bound (Lemma 4.1): a message of at most $kw/16$ bits cannot carry the $k$ fresh words written in an epoch.
--
--   Differences from the source:
--   - encoding: X₁, …, X_k independent uniform w-bit words; J uniform in [k] → X uniform on Fin k → BitVec w, J uniform on Fin k, with [NeZero k] and 0 < w; reason: the same law; k ≥ 1 is needed for J, and w ≥ 1 for the printed 1/w
--   - encoding: an encoder and a decoder → deterministic functions enc : X → Z → BitVec β and dec : BitVec β → Z → Fin k → BitVec w, for side information of any type and law; reason: private randomness of either party can be put into Z, which only helps the decoder, so this covers randomized ones
--   - encoding: recovers X_J with probability s only if s ≤ β/(kw) + 1/w → the success probability raeSuccess (in [0, 1] ⊆ ENNReal) is at most ENNReal.ofReal(β/(kw) + 1/w); reason: 'with probability s only if' is an upper bound on the success probability
-- source:
--   Ciszewski, Ragnoli, Access Cost Tradeoffs in Mixed-Mode Oblivious RAM, STOC 2027 submission (manuscript sha256 a4f849fd…), pp. 14–15, Lemma A.2

import Mathlib
import Definitions.Def_MixedORAM_PublicRead_RandomAccessCode

set_option autoImplicit false

namespace MixedORAM.PublicRead

theorem lemma_A_2 {ζ : Type} (k w β : ℕ) [NeZero k] (hw : 0 < w) (μ : PMF ζ)
    (enc : (Fin k → BitVec w) → ζ → BitVec β) (dec : BitVec β → ζ → Fin k → BitVec w) :
    raeSuccess k w β μ enc dec ≤ ENNReal.ofReal ((β : ℝ) / ((k : ℝ) * w) + 1 / (w : ℝ)) ∧
      ((β : ℝ) ≤ (k : ℝ) * w / 16 → 4 ≤ w →
        raeSuccess k w β μ enc dec ≤ ENNReal.ofReal (5 / 16)) := by sorry

end MixedORAM.PublicRead
