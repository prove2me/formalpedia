-- Prove2me | Theorems.Thm_IntADSat_lemma_S3_3
-- name    : IntADSat.lemma_S3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:52:07.589305+00:00
-- url     : https://prove2.me/theorems/d20cbdd7-2b1f-426f-ac63-ed6d29b2b136
-- title:
--   Lemma S3.3 — degree residue classes are small
-- statement:
--   For $n\ge2^{16}$ and $128\le p\le n$, put
--
--   $$
--   m_p(G)=\max_{a\in\mathbb Z/p\mathbb Z}|\{v:\deg_G(v)\equiv a\pmod p\}|,\qquad b_p=\Big\lceil32\Big(\frac np+\sqrt n\Big)\Big\rceil .
--   $$
--
--   Then, for $G\sim G(n,1/2)$,
--
--   $$
--   \Pr\big[\exists\,p\in\mathbb Z,\ 128\le p\le n:\ m_p(G)\ge b_p\big]\le n^2(e/8)^{32\sqrt n}.
--   $$
--
--   The moduli $p$ range over all integers in $[128,n]$, not only primes.
--
--   Differences from the source:
--   - encoding: p ∈ ℤ with 128 ≤ p ≤ n → p : ℕ with 128 ≤ p ≤ n; reason: same moduli
--   - encoding: max over a ∈ ℤ/pℤ of #{v : deg v ≡ a (mod p)} → max over a ∈ {0, …, p − 1} of #{v : deg v % p = a}; reason: same residues
--   - encoding: G ∼ G(n, 1/2) on the labelled vertex set [n] → erProb n (1/2) on SimpleGraph (Fin n) (published Erdős–Rényi product weight at edge probability 1/2); reason: same law: every labelled graph has probability 2^(−n(n−1)/2)
-- source:
--   Z. Lu, Integral saturation of adjacency-degree lattices, arXiv:2611.01838 (held version, sha256 d1acbc32…3631145), Lemma S3.3, p.36 (PDF 37)

import Mathlib
import Definitions.Def_LPCommunity_SBMRecovery_Setting
import Definitions.Def_IntADSat_maxResidue
import Definitions.Def_IntADSat_bP

set_option autoImplicit false

namespace IntADSat

/-- **Lemma S3.3** (Z. Lu, *Integral saturation of adjacency-degree lattices*, arXiv:2611.01838 (held version, sha256 d1acbc32…3631145), p.36 (PDF 37)). For `n ≥ 2¹⁶` and `128 ≤ p ≤ n`, put
`m_p(G) = max_{a ∈ ℤ/pℤ} |{v : deg_G(v) ≡ a (mod p)}|` and `b_p = ⌈32(n/p + √n)⌉`. Then for
`G ∼ G(n, 1/2)`, `Pr[∃ p ∈ ℤ, 128 ≤ p ≤ n : m_p(G) ≥ b_p] ≤ n²(e/8)^{32√n}`.

**Formalization Note** `p` ranges over all integer moduli in `[128, n]`, not only primes, as printed. -/
theorem lemma_S3_3 (n : ℕ) (hn : 2 ^ 16 ≤ n) :
    LPCommunity.SBMRecovery.erProb n (1 / 2) (fun G => ∃ p : ℕ, 128 ≤ p ∧ p ≤ n ∧ bP n p ≤ maxResidue p G) ≤
      (n : ℝ) ^ 2 * (Real.exp 1 / 8) ^ (32 * Real.sqrt n) := by sorry

end IntADSat
