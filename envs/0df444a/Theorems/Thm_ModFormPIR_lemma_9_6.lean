-- Prove2me | Theorems.Thm_ModFormPIR_lemma_9_6
-- name    : ModFormPIR.lemma_9_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:02:14.821726+00:00
-- url     : https://prove2.me/theorems/463cc627-f3ed-48fd-bb57-3d21c73eb76c
-- title:
--   Lemma 9.6, p.36 — PIR for $n$-bit databases, with $n+1$ stored bits per server
-- statement:
--   Fix integers $s,b\ge2$. Let $n$ be sufficiently large and $d$ the largest integer with $b^d\le n$. Suppose there are integers $B,p$ with $p$ prime, $p\ge n^4$, $2^B\le p\le2^B(1+\frac1{4n})$, $B,\log p\le\mathrm{polylog}(n)$. Suppose moreover that for every $j\in[d]$ there is an information-theoretically private $s$-server PIR scheme over databases of $b^j$ records in $\mathbb F_p$, where each server stores $b^j$ elements of $\mathbb F_p$, computed in $b^j\,\mathrm{polylog}(n)$ time, the user uploads $O(\log n)$ bits, and each server reads and sends back at most $k$ elements of $\mathbb F_p$ in $k\,\mathrm{polylog}(n)$ time. Then there is an information-theoretically private $s$-server PIR scheme for arbitrary $n$-bit databases with $n+1$ stored bits per server, $n\,\mathrm{polylog}(n)$ preprocessing, $O(\log^2n)$ upload, and $k\,\mathrm{polylog}(n)$ server time and download. In particular, if $k\le n^{\eta+o(1)}$ for a constant $\eta$, this is an $s$-server scheme with exponent $\eta$.
--
--   This compiler is the bridge from the field-record schemes of Theorem 7.1 to Definition 5.1.
--
--   **Formalization Note** "Polylog" needs a family, so the hypothesis is one family of programs for all large $n$ (`FieldScheme.Realizes`).
--
--   Differences from the source:
--   - generalization: "at most n + 1 stored bits per server" → exactly n + 1 bits; reason: padding gives exactness, and exactly n + 1 implies at most n + 1; it is the form Definition 5.1 needs
--   - generalization: hypothesis: "reads and sends back at most k elements of 𝔽_p" → hypothesis: reads at most k·size(p) bits of the element table, not necessarily whole elements; reason: any scheme reading k elements meets it, and the proof’s per-access decoding handles single bits
--   - reading: "Suppose there are integers B, p" for a given n, and schemes for each j → one FieldScheme whose sampler outputs B, p, with programs and constants for all n ≥ n₀; reason: the conclusion is a uniform scheme per Definition 5.1, which needs public parameters sampled in expected polylog time
--   - encoding: n^{ρ+o(1)}, polylog(n), O(log² n) → (n+1)^{ρ+g n} with one g → 0, C·L^K, C·L² with L = ⌊log₂(n+2)⌋+1; reason: the meaning of the asymptotics; n+1 avoids 1^x = 1 at n = 1 and changes no exponent
-- source:
--   Henzinger, Ragavan, Doubly-Efficient Private Information Retrieval from Modular Forms, STOC 2027 submission (manuscript sha256 2442f3db…), Lemma 9.6, p.36 (PDF pp.40–41)

import Mathlib
import Definitions.Def_ModFormPIR_Layouts

open Filter Topology

set_option autoImplicit false

namespace ModFormPIR

/-- **Lemma 9.6** (PIR for `n`-bit databases), p.36. Henzinger, Ragavan, *Doubly-Efficient Private Information Retrieval from Modular Forms*, STOC 2027 submission (manuscript sha256 2442f3db…).
From PIR schemes over `b^j` records of `𝔽_p` with `p` just above a power of two, to a PIR scheme for arbitrary `n`-bit databases: `n + 1` stored
bits per server, `n·polylog(n)` preprocessing, `O(log² n)` upload, and `k·polylog(n)` server time and download. If `k ≤ n^{η+o(1)}`, this is a scheme with
exponent `η`.

**Formalization Note.** "Polylog" needs a family, so the hypothesis is one `FieldScheme` on the machine for all large `n`, its sampler producing `B, p`: the printed
lemma supposes `B, p` are given, while its last sentence, by Definition 5.1, needs them sampled. The printed "at most `n+1`" bits is stated as exactly
`n + 1` (padding), as in Definition 5.1. The conclusion's budget `k·L^{K₁}` covers both time and download. -/
theorem lemma_9_6 (s b : ℕ) (hs : 2 ≤ s) (hb : 2 ≤ b) (F : FieldScheme s b) (n₀ b₀ C K : ℕ)
    (hF : ∀ n ≥ n₀, ∀ W ≥ b₀ * (Nat.log2 n + 1), F.Realizes n C K W) :
    (∃ (S : Scheme s) (n₁ b₁ C₁ K₁ : ℕ), ∀ n ≥ n₁, ∀ W ≥ b₁ * (Nat.log2 n + 1),
      S.Realizes n C₁ K₁ ((F.k n : ℝ) * (polyL n : ℝ) ^ K₁) W) ∧
    ∀ η : ℝ, (∃ g : ℕ → ℝ, Tendsto g atTop (𝓝 0) ∧
        ∀ n ≥ n₀, (F.k n : ℝ) ≤ ((n : ℝ) + 1) ^ (η + g n)) →
      HasScheme s η := by sorry

end ModFormPIR
