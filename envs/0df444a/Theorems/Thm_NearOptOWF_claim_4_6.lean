-- Prove2me | Theorems.Thm_NearOptOWF_claim_4_6
-- name    : NearOptOWF.claim_4_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:52:20.330827+00:00
-- url     : https://prove2.me/theorems/ddeba9ff-ecb6-4c8e-89e3-28a090492b15
-- title:
--   Claim 4.6 — $\mathcal H = \{i\mathcal O(F)\}$ and $\mathcal H' = \{i\mathcal O(G\circ H)\}$ are $2^n\cdot 2^{-\lambda^{\Omega(1)}}\cdot\mathrm{poly}(n) + 2^{-8n}$ indistinguishable
-- statement:
--   Let $i\mathcal O$ be a sub-exponentially secure indistinguishability obfuscator and $F, G, H$ sub-exponentially secure puncturable PRFs. Let
--   $$
--   \mathcal H = \{ i\mathcal O(F) \}, \qquad \mathcal H' = \{ i\mathcal O(G \circ H) : G : \{0,1\}^N \to \{0,1\}^m,\ H : \{0,1\}^n \to \{0,1\}^N \}, \quad N = 10n,
--   $$
--   both obfuscated at security parameter $\lambda(n)$ and padded to size $S(n)$. There are $c > 0$, an exponent $k_0$, a polynomial $q$ and a polynomial size threshold $S_0$ such that for all polynomially bounded $\lambda(n) \ge n^{k_0}$, $m(n)$ and $S(n) \ge S_0(\lambda(n) + n + m(n))$, and every polynomial $p$: for all sufficiently large $n$ and every distinguisher circuit $D$ of size at most $p(n)$,
--   $$
--   \Bigl|\Pr_{f \leftarrow \mathcal H}[D(f) = 1] - \Pr_{f \leftarrow \mathcal H'}[D(f) = 1]\Bigr| \le 2^n \cdot 2^{-\lambda(n)^{c}} \cdot q(n) + 2^{-8n}.
--   $$
--
--   This is the first step of the proof of Theorem 4.1: it reduces one-wayness of $\mathcal H$ to one-wayness of $\mathcal H'$.
--
--   Differences from the source:
--   - reading: security parameter λ "a sufficiently large polynomial λ = poly(n, m)" and padding "with sufficiently many dummy gates" → λ(n), S(n), m(n) polynomially bounded with λ(n) ≥ n^{k₀} and S(n) ≥ S₀(λ(n) + n + m(n)), k₀ and S₀ existential; reason: the paper leaves the polynomial λ and the padded size to be chosen large enough
--   - reading: 2^{-λ^{Ω(1)}}, poly(n), "computationally indistinguishable" → ∃ c > 0, polynomial q before the distinguisher; every polynomial-size distinguisher, for all sufficiently large n; reason: the hidden constants come from the primitives' δ's
--   - reading: sub-exponentially secure indistinguishability obfuscator (Definition 3.4, "PPT (resp. polynomial-size) distinguisher", "poly(ε)" advantage) → multi-output circuits, perfect correctness for every coin string, security against non-uniform circuits of size ≤ p(λ) on functionally equivalent pairs of equal size with n ≤ p(λ), advantage ≤ 2^{-λ^δ} for some δ > 0; reason: the proof of Claim 4.7 (p.19) uses the non-uniform variant; equal size is the paper's padding (pp.11–12) and without it no iO exists; ∃δ absorbs poly(ε)
--   - reading: sub-exponentially secure puncturable PRF (never defined in the paper) → standard Sahai–Waters/[CCR16] definition with parameters (λ, n, m): polynomial-time key, puncturing and evaluation, punctured correctness, non-uniform selective security with advantage ≤ 2^{-λ^δ}; reason: the paper uses the primitive without a definition; this is the standard one with §3's sub-exponential security
-- source:
--   Ilango–Lombardi–Tu, Near-Optimal One-Way Functions, Direct Product Hardness and Hash Functions from iO and NP versus coNP, STOC 2027 submission (manuscript of 2026-11-03, sha256 91ede246…), Claim 4.6, p.15 (PDF p.17); H′ defined on p.14 (PDF p.16)

import Mathlib
import Definitions.Def_NearOptOWF_MIOScheme_IsSubexpIO
import Definitions.Def_NearOptOWF_PPRF_IsSubexpPPRF
import Definitions.Def_NearOptOWF_famH
import Definitions.Def_NearOptOWF_famHprime

namespace NearOptOWF

open LaconicBarrier

/-- **Claim 4.6** (Ilango–Lombardi–Tu, *Near-Optimal One-Way Functions, Direct Product Hardness and Hash Functions from iO and NP versus coNP*, STOC 2027 submission (manuscript of 2026-11-03, sha256 91ede246…), Claim 4.6, p.15 (PDF p.17); `H′` defined on p.14 (PDF p.16)): let `iO` be a
sub-exponentially secure indistinguishability obfuscator and `F, G, H` sub-exponentially secure
puncturable PRFs. There are `c > 0`, an exponent `k₀`, a polynomial `q` and a polynomial size threshold
`S₀` such that, for all polynomially bounded `λ(n) ≥ n^{k₀}`, `m(n)` and padded sizes `S(n) ≥ S₀(λ(n) + n
+ m(n))`, every polynomial-size distinguisher tells `H = {iO(F)}` from `H′ = {iO(G ∘ H)}` (`N = 10n`) with
advantage at most `2ⁿ · 2^{−λ^c} · q(n) + 2^{−8n}` for all sufficiently large `n`.

**Formalization Note** "`2^{−λ^{Ω(1)}}`", "`poly(n)`" and the "sufficiently large polynomial `λ`" of
p.11 are `∃ c, q, k₀` placed before the distinguisher; `S₀` is the common padded size of p.12. The
constants `2^{−8n}` and `N = 10n` are the paper's. -/
theorem claim_4_6 (O : MIOScheme) (hO : O.IsSubexpIO) (F G H : PPRF) (hF : F.IsSubexpPPRF)
    (hG : G.IsSubexpPPRF) (hH : H.IsSubexpPPRF) :
    ∃ c : ℝ, 0 < c ∧ ∃ (k₀ : ℕ) (q S₀ : Polynomial ℕ), ∀ lam S m : ℕ → ℕ,
      (∃ r : Polynomial ℕ, ∀ n, lam n ≤ r.eval n ∧ S n ≤ r.eval n ∧ m n ≤ r.eval n) →
      (∀ n, n ^ k₀ ≤ lam n) → (∀ n, S₀.eval (lam n + n + m n) ≤ S n) →
      ∀ p : Polynomial ℕ, ∀ᶠ n : ℕ in Filter.atTop, ∀ (k : ℕ) (D : MCircuit k), D.size ≤ p.eval n →
        |coinAvg ((famH O F lam S m).coins n)
            (fun ρ => accepts D ((famH O F lam S m).samp n ρ).code) -
          coinAvg ((famHprime O G H lam S m).coins n)
            (fun ρ => accepts D ((famHprime O G H lam S m).samp n ρ).code)| ≤
          2 ^ n * (2 : ℝ) ^ (-((lam n : ℕ) : ℝ) ^ c) * ((q.eval n : ℕ) : ℝ) + (2 : ℝ) ^ (-(8 * n : ℝ)) := by sorry

end NearOptOWF
