-- Prove2me | Theorems.Thm_MultiphaseDisj_claim_4_3
-- name    : MultiphaseDisj.claim_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:29:11.898387+00:00
-- url     : https://prove2.me/theorems/b76595ed-32d4-4b6a-8cf4-5489aa5522e1
-- title:
--   Claim 4.3 — two counting facts for uniform $s$-sets
-- statement:
--   Let $1\le s\le N$, let $\mathcal S=\binom{[N]}{s}$ and let $U$ be the uniform distribution on $\mathcal S$.
--
--   1. (a) For every $P\subseteq[N]$ and every integer $k\ge1$,
--   $$
--   \Pr_{a\sim U}\big[|a\cap P|\ge k\big]\le\binom{|P|}{k}\Big(\frac sN\Big)^k\le\Big(\frac{e|P|s}{kN}\Big)^k .
--   $$
--   2. (b) For every $V\subseteq[N]$,
--   $$
--   \Pr_{a\sim U}\big[a\cap V=\emptyset\big]\le\Big(1-\frac{|V|}N\Big)^s\le e^{-s|V|/N}.
--   $$
--
--   These are the estimates behind the two counting steps of the corruption bound: few uniform $s$-sets meet a small set in many points, and few avoid a large set.
--
--   Differences from the source:
--   - encoding: [N] and the uniform distribution on ([N] choose s) → Fin N and the uniform law on powersetCard s univ; reason: same instances
-- source:
--   Ko, Unconditional Boolean Dynamic Lower Bounds from Disjointness, arXiv:2610.10904 (held version, sha256 ba26649b…), Claim 4.3, p.25 (proof pp.25–26)

import Mathlib
import Definitions.Def_MultiphaseDisj_Rectangle

set_option autoImplicit false

namespace MultiphaseDisj

/-- **Claim 4.3 (Two counting facts)** (Ko, *Unconditional Boolean Dynamic Lower Bounds from Disjointness*, arXiv:2610.10904, held
version sha256 ba26649b…, Claim 4.3, p.25). Write `S := ([N] choose s)` and let
`U` be the uniform distribution on `S`. Let `1 ≤ s ≤ N`.

* (a) For every `P ⊆ [N]` and every integer `k ≥ 1`,
  `Pr_{a∼U}[|a ∩ P| ≥ k] ≤ (|P| choose k) (s/N)^k ≤ (e|P|s/(kN))^k`.
* (b) For every `V ⊆ [N]`, `Pr_{a∼U}[a ∩ V = ∅] ≤ (1 − |V|/N)^s ≤ e^{−s|V|/N}`.

**Formalization Note** `[N]` is `Fin N`; `S` is `Finset.powersetCard s univ`. -/
theorem claim_4_3 (N s : ℕ) (hs : 1 ≤ s) (hsN : s ≤ N) :
    (∀ (P : Finset (Fin N)) (k : ℕ), 1 ≤ k →
      pr (unif (Finset.powersetCard s (Finset.univ : Finset (Fin N))))
          (fun a => k ≤ (a ∩ P).card) ≤
        (P.card.choose k : ℝ) * ((s : ℝ) / N) ^ k ∧
      (P.card.choose k : ℝ) * ((s : ℝ) / N) ^ k ≤
        (Real.exp 1 * P.card * s / (k * N)) ^ k) ∧
    (∀ V : Finset (Fin N),
      pr (unif (Finset.powersetCard s (Finset.univ : Finset (Fin N))))
          (fun a => Disjoint a V) ≤ (1 - (V.card : ℝ) / N) ^ s ∧
      (1 - (V.card : ℝ) / N) ^ s ≤ Real.exp (-((s : ℝ) * V.card / N))) := by sorry

end MultiphaseDisj
