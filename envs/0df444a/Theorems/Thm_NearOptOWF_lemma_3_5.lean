-- Prove2me | Theorems.Thm_NearOptOWF_lemma_3_5
-- name    : NearOptOWF.lemma_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:50:29.665338+00:00
-- url     : https://prove2.me/theorems/47b74ab7-3815-4379-8ad0-aee185e93ac3
-- title:
--   Lemma 3.5 (corrected: common padded size) — obfuscated puncturable PRFs are indistinguishable (Canetti–Chen–Reyzin)
-- statement:
--   Let $F, G$ be sub-exponentially secure puncturable PRFs and $i\mathcal O$ a sub-exponentially secure indistinguishability obfuscator. There are $c > 0$, a polynomial $q$ and a polynomial size threshold $S_0$ such that for every polynomial $p$ and all sufficiently large $\lambda$: for all $n, m \le p(\lambda)$, every common size $S$ with $S_0(\lambda + n + m) \le S \le p(\lambda)$ and every distinguisher circuit $D$ of size at most $p(\lambda)$,
--   $$
--   \Bigl|\Pr_{k, \rho}\bigl[D(i\mathcal O(\mathrm{pad}_S F_k;\rho)) = 1\bigr] - \Pr_{k', \rho}\bigl[D(i\mathcal O(\mathrm{pad}_S G_{k'};\rho)) = 1\bigr]\Bigr| \le q(n)\cdot 2^n \cdot 2^{-\lambda^{c}} .
--   $$
--
--   The lemma is used in the proof of Claim 4.6 to switch from $\mathcal H = \{i\mathcal O(F)\}$ to $\mathcal H' = \{i\mathcal O(G \circ H)\}$.
--
--   Differences from the source:
--   - correction: iO(F) and iO(G) are poly(n)·2ⁿ·2^{-λ^{Ω(1)}} indistinguishable, with no condition on circuit sizes → the obfuscated circuits are padded to a common size S ≥ S₀(λ + n + m); reason: as printed the lemma is false under its own hypotheses: an obfuscator appending |C| in binary is still a sub-exponentially secure iO, G := F plus one dummy gate is still a puncturable PRF, and the trailer separates iO(F) from iO(G) with advantage 1; the paper pads every obfuscated circuit (pp.11–12)
--   - reading: sub-exponentially secure iO → non-uniform, equal-size pairs, perfect correctness, ∃δ (see the definition); reason: Definition 3.4 with the proof's own use (p.19)
--   - reading: sub-exponentially secure puncturable PRF (undefined) → standard definition with non-uniform selective security; reason: the paper gives no definition
--   - reading: 2^{-λ^{Ω(1)}}, poly(n), "computationally indistinguishable" → ∃ c > 0 and a polynomial q placed before the distinguisher; every polynomial p bounds n, m, S and |D| for all large λ; reason: the hidden constants come from the primitives' δ's, not from the distinguisher
-- source:
--   Ilango–Lombardi–Tu, Near-Optimal One-Way Functions, Direct Product Hardness and Hash Functions from iO and NP versus coNP, STOC 2027 submission (manuscript of 2026-11-03, sha256 91ede246…), Lemma 3.5, p.9 (PDF p.11), citing [CCR16, Lemma 4.5]

import Mathlib
import Definitions.Def_NearOptOWF_MIOScheme_IsSubexpIO
import Definitions.Def_NearOptOWF_PPRF_IsSubexpPPRF
import Definitions.Def_NearOptOWF_obfPad

namespace NearOptOWF

open LaconicBarrier

/-- **Lemma 3.5 (Canetti–Chen–Reyzin), corrected: common padded size** (Ilango–Lombardi–Tu, *Near-Optimal One-Way Functions, Direct Product Hardness and Hash Functions from iO and NP versus coNP*, STOC 2027 submission (manuscript of 2026-11-03, sha256 91ede246…), Lemma 3.5, p.9 (PDF
p.11), citing [CCR16, Lemma 4.5]): let `F, G` be sub-exponentially secure puncturable PRFs and `iO` a
sub-exponentially secure indistinguishability obfuscator. There are `c > 0`, a polynomial `q` and a
polynomial size threshold `S₀` such that for every polynomial `p`, for all sufficiently large `λ`, all
`n, m ≤ p(λ)`, every common size `S` with `S₀(λ + n + m) ≤ S ≤ p(λ)` and every distinguisher `D` of size
at most `p(λ)`, the obfuscations `iO(padTo S F_k)` and `iO(padTo S G_{k'})` (uniform keys and coins) are
told apart by `D` with advantage at most `q(n) · 2ⁿ · 2^{−λ^c}`.

**Formalization Note** As printed (without a common size) the lemma is refuted by its own
hypotheses: an obfuscator that appends `|C|` in binary is still a sub-exponentially secure iO, and `G
= F` plus one dummy gate is still a puncturable PRF, so `iO(F)` and `iO(G)` differ in a readable
trailer. The correction pads both to a common size above the sizes of the hybrids' punctured circuits,
as the paper pads every obfuscated circuit (pp.11–12). `2^{−λ^{Ω(1)}}` and `poly(n)` are `∃ c, q`
placed before the distinguisher. -/
theorem lemma_3_5 (O : MIOScheme) (hO : O.IsSubexpIO) (F G : PPRF) (hF : F.IsSubexpPPRF)
    (hG : G.IsSubexpPPRF) :
    ∃ c : ℝ, 0 < c ∧ ∃ q S₀ : Polynomial ℕ, ∀ p : Polynomial ℕ, ∀ᶠ lam : ℕ in Filter.atTop,
      ∀ n m : ℕ, n ≤ p.eval lam → m ≤ p.eval lam →
      ∀ S : ℕ, S₀.eval (lam + n + m) ≤ S → S ≤ p.eval lam →
      ∀ (k : ℕ) (D : MCircuit k), D.size ≤ p.eval lam →
        |coinAvg (F.keyLen lam n m) (fun key => coinAvg (O.coins lam n S) (fun ρ =>
            accepts D (obfPad O lam n S (F.circ lam n m key) ρ).code)) -
          coinAvg (G.keyLen lam n m) (fun key => coinAvg (O.coins lam n S) (fun ρ =>
            accepts D (obfPad O lam n S (G.circ lam n m key) ρ).code))| ≤
          ((q.eval n : ℕ) : ℝ) * 2 ^ n * (2 : ℝ) ^ (-(lam : ℝ) ^ c) := by sorry

end NearOptOWF
