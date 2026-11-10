-- Prove2me | Theorems.Thm_NearOptOWF_claim_4_7
-- name    : NearOptOWF.claim_4_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:53:21.106231+00:00
-- url     : https://prove2.me/theorems/0ee9b203-d6c2-4566-bf8b-4695cf595e49
-- title:
--   Claim 4.7 — the pre-image sampler $A$ is PPT, succeeds with probability $2^{n^{2\delta}-m}$, and is approximately functionally equivalent and uniform on pre-images
-- statement:
--   Let $i\mathcal O$ be a sub-exponentially secure indistinguishability obfuscator, $G, H$ sub-exponentially secure puncturable PRFs, $m$ an admissible output length, $\delta > 0$ and $A^*$ a PPT inverter. The **pre-image sampler** $A(g, y)$ samples $H : \{0,1\}^n \to \{0,1\}^N$ ($N = 10n$), runs $A^*(i\mathcal O(g \circ H), y) \to x$, and outputs $H(x)$ if $g(H(x)) = y$, otherwise $\perp$. Then:
--
--   1. **PPT:** for polynomially bounded, polynomial-time computable $\lambda(n)$ and $S(n)$, $A$ uses polynomially many coins and is computed by one polynomial-time machine.
--
--   Moreover there are $c > 0$, an exponent $k_0$ and a polynomial size threshold $S_0$ such that for all polynomially bounded $\lambda(n) \ge (n + m(n))^{k_0}$ and $S(n) \ge S_0(\lambda(n) + n + m(n))$:
--
--   2. **Success probability:** for all sufficiently large $n$, if $A^*$ inverts $\mathcal H'$ with probability more than $2^{n^{3\delta} - \min\{n,m\}}$, then
--   $$
--   \Pr_{G,\ y \leftarrow \{0,1\}^m}\bigl[A(G, y) \in G^{-1}(y)\bigr] \ge 2^{n^{2\delta} - m};
--   $$
--   3. **Functional equivalence:** for every polynomial $p$ and all large $n$, if $g, g'$ are functionally equivalent circuits of size at most $p(n)$ with $|g| + S_0 \le S(n)$ and $|g'| + S_0 \le S(n)$, then for every $y \in \{0,1\}^*$, $A(g, y)$ and $A(g', y)$ are at most $2^N \cdot 2^{-\lambda^{c}}$-far;
--   4. **Uniformity on pre-images:** for every polynomial $p$, all large $n$, every circuit $g$ of size at most $p(n)$ with $|g| + S_0 \le S(n)$ and every $y \in \mathrm{Im}(g)$, the distribution of $A(g, y)$ is at most $2^N \cdot 2^{-\lambda^{c}}$-far from the distribution that outputs $\perp$ with probability $\Pr[A(g, y) = \perp]$ and otherwise a uniform pre-image from $g^{-1}(y)$.
--
--   The claim makes $A$ an approximate perfect pre-image sampler (Definition 4.2), which Claims 4.8 and 4.9 turn into an Arthur–Merlin protocol for unsatisfiability.
--
--   Differences from the source:
--   - reading: "A* is a PPT algorithm breaking the 2^{n^{3δ}−min{n,m}}-security of H′" then A succeeds with probability at least 2^{n^{2δ}−m} → for all sufficiently large n: if the inversion probability of A* at n exceeds 2^{n^{3δ}−min{n,m}}, then A's success probability at n is at least 2^{n^{2δ}−m}; reason: the proof bounds the success at the same n at which A* breaks; this gives the bound for infinitely many n whenever A* breaks the security infinitely often
--   - generalization: PPT, functional equivalence and uniformity under the assumption that A* breaks the 2^{n^{3δ}−min{n,m}}-security of H′ → stated for every PPT A*, without that assumption; reason: the proofs of these three conditions (pp.19–20) never use that A* breaks the security; the printed claim is the case of a breaking A*
--   - generalization: g, g′ : {0,1}^N → {0,1}^m → circuits with N inputs and any number of outputs; reason: the proof never uses the output length; circuits with m outputs are a special case
--   - reading: polynomial-size circuits g, g′ (obfuscated as iO(g ∘ H) padded to the common size) → size ≤ p(n) for every polynomial p, and |g| + S₀(λ(n) + n + m(n)) ≤ S(n); reason: A pads iO(g ∘ H) to S(n) (pp.11–12), so g must fit the padding together with H and the hybrids' punctured circuits
--   - reading: 2^{-λ^{Ω(1)}} and "sufficiently large polynomial λ" → ∃ c > 0, k₀, S₀ placed before g, y; λ(n) ≥ (n + m(n))^{k₀}; reason: the hidden constants come from the primitives' δ's
--   - reading: "A is a PPT algorithm" → the coin count is polynomial in the input length and one machine (PolyTimeOn) computes A's output from (1ⁿ, g, y) and its coins, for polynomial-time computable λ(n), S(n); reason: the published uniform machine model
--   - reading: sub-exponentially secure indistinguishability obfuscator (Definition 3.4, "PPT (resp. polynomial-size) distinguisher", "poly(ε)" advantage) → multi-output circuits, perfect correctness for every coin string, security against non-uniform circuits of size ≤ p(λ) on functionally equivalent pairs of equal size with n ≤ p(λ), advantage ≤ 2^{-λ^δ} for some δ > 0; reason: the proof of Claim 4.7 (p.19) uses the non-uniform variant; equal size is the paper's padding (pp.11–12) and without it no iO exists; ∃δ absorbs poly(ε)
--   - reading: sub-exponentially secure puncturable PRF (never defined in the paper) → standard Sahai–Waters/[CCR16] definition with parameters (λ, n, m): polynomial-time key, puncturing and evaluation, punctured correctness, non-uniform selective security with advantage ≤ 2^{-λ^δ}; reason: the paper uses the primitive without a definition; this is the standard one with §3's sub-exponential security
--   - encoding: outputs ⊥ or a string of {0,1}^N → distributions on Option (Fin N → Bool), ⊥ = none; reason: Lean convention; same distributions
-- source:
--   Ilango–Lombardi–Tu, Near-Optimal One-Way Functions, Direct Product Hardness and Hash Functions from iO and NP versus coNP, STOC 2027 submission (manuscript of 2026-11-03, sha256 91ede246…), Claim 4.7, p.15 (PDF p.17); the sampler A on the same page

import Mathlib
import Definitions.Def_NearOptOWF_MIOScheme_IsSubexpIO
import Definitions.Def_NearOptOWF_PPRF_IsSubexpPPRF
import Definitions.Def_NearOptOWF_Inverter_IsPPT
import Definitions.Def_NearOptOWF_IsPolyLen
import Definitions.Def_NearOptOWF_famHprime
import Definitions.Def_NearOptOWF_invProb
import Definitions.Def_NearOptOWF_sampA
import Definitions.Def_NearOptOWF_idealDist
import Definitions.Def_HybridXorLift_tvDist
import Definitions.Def_NearOptOWF_FunEquiv

namespace NearOptOWF

open LaconicBarrier

/-- **Claim 4.7** (Ilango–Lombardi–Tu, *Near-Optimal One-Way Functions, Direct Product Hardness and Hash Functions from iO and NP versus coNP*, STOC 2027 submission (manuscript of 2026-11-03, sha256 91ede246…), Claim 4.7, p.15 (PDF p.17); the pre-image sampler `A` on the same page):
let `iO` be a sub-exponentially secure indistinguishability obfuscator, `G, H` sub-exponentially secure
puncturable PRFs, `m` a polynomially bounded polynomial-time computable length, `δ > 0`, and `A*` a PPT
inverter. Then the sampler `A(g, y)` (sample `H`, run `A*(iO(g ∘ H), y) → x`, output `H(x)` if
`g(H(x)) = y`, else `⊥`) satisfies:

1. *PPT*: for polynomially bounded, polynomial-time computable `λ(n)` and `S(n)`, `A` uses polynomially
   many coins and one machine computes its output from `(1ⁿ, g, y)` and its coins in polynomial time;

and there are `c > 0`, an exponent `k₀` and a polynomial size threshold `S₀` such that, for all
polynomially bounded `λ(n) ≥ (n + m(n))^{k₀}` and `S(n) ≥ S₀(λ(n) + n + m(n))`, with `N = 10n`:

2. *success probability*: for all sufficiently large `n`, if `A*` inverts `H′` with probability more
   than `2^{n^{3δ} − min{n, m}}`, then for a uniform `y ← {0,1}ᵐ` and a uniform key of `G`, `A(G, y)`
   outputs a pre-image in `G⁻¹(y)` with probability at least `2^{n^{2δ} − m}`;
3. *functional equivalence*: for every polynomial `p` and all sufficiently large `n`, if `g, g'` are
   functionally equivalent circuits of size at most `p(n)` that fit the padding (`|g| + S₀ ≤ S(n)`),
   then for every `y ∈ {0,1}*`, `A(g, y)` and `A(g', y)` are at most `2^N · 2^{−λ^c}`-far;
4. *uniformity on pre-images*: for every polynomial `p`, all sufficiently large `n`, every circuit `g`
   of size at most `p(n)` that fits the padding and every `y ∈ Im(g)`, `A(g, y)` is at most
   `2^N · 2^{−λ^c}`-far from the distribution that outputs `⊥` with probability `Pr[A(g, y) = ⊥]` and
   otherwise a uniform pre-image from `g⁻¹(y)`.

**Formalization Note** "Breaking the `2^{n^{3δ}−min{n,m}}`-security" is the inversion probability
exceeding that bound; the success bound is stated at every sufficiently large `n` where it does, which
gives it for infinitely many `n` when `A*` breaks the security infinitely often. `2^{−λ^{Ω(1)}}` and
"sufficiently large polynomial `λ`" are `∃ c, k₀` placed before `g, y`. Clauses 1, 3 and 4 do not assume that `A*` breaks the
security (their proofs never use it). The obfuscated circuit is padded to `S(n)` (pp.11–12). -/
theorem claim_4_7 (O : MIOScheme) (hO : O.IsSubexpIO) (G H : PPRF) (hG : G.IsSubexpPPRF)
    (hH : H.IsSubexpPPRF) (m : ℕ → ℕ) (hm : IsPolyLen m) (δ : ℝ) (hδ : 0 < δ) (Astar : Inverter)
    (hA : Astar.IsPPT) :
    (∀ lam S : ℕ → ℕ, IsPolyLen lam → IsPolyLen S →
      (∃ q : Polynomial ℕ, ∀ (n : ℕ) (g : MCircuit (10 * n)) (y : List Bool)
          (k₂ : Fin (H.keyLen (lam n) n (10 * n)) → Bool) (ρ : Fin (O.coins (lam n) n (S n)) → Bool),
          H.keyLen (lam n) n (10 * n) + O.coins (lam n) n (S n) +
              Astar.coins (KarpLiptonOM.tupleEnc (sampInput O H (lam n) (S n) n g y k₂ ρ)).length ≤
            q.eval (KarpLiptonOM.tupleEnc [unary n, g.code, y]).length) ∧
      PolyTimeOn (ι := (n : ℕ) × (g : MCircuit (10 * n)) × (y : List Bool) ×
          (k₂ : Fin (H.keyLen (lam n) n (10 * n)) → Bool) × (ρ : Fin (O.coins (lam n) n (S n)) → Bool) ×
          (Fin (Astar.coins (KarpLiptonOM.tupleEnc (sampInput O H (lam n) (S n) n g y k₂ ρ)).length) →
            Bool))
        (fun i => [unary i.1, i.2.1.code, i.2.2.1, bits i.2.2.2.1, bits i.2.2.2.2.1, bits i.2.2.2.2.2])
        (fun i => match sampRun O H Astar (lam i.1) (S i.1) i.1 i.2.1 i.2.2.1 i.2.2.2.1 i.2.2.2.2.1
            (bits i.2.2.2.2.2) with
          | none => [false]
          | some z => true :: z)) ∧
    ∃ c : ℝ, 0 < c ∧ ∃ (k₀ : ℕ) (S₀ : Polynomial ℕ), ∀ lam S : ℕ → ℕ,
      (∃ r : Polynomial ℕ, ∀ n, lam n ≤ r.eval n ∧ S n ≤ r.eval n) →
      (∀ n, (n + m n) ^ k₀ ≤ lam n) → (∀ n, S₀.eval (lam n + n + m n) ≤ S n) →
      (∀ᶠ n : ℕ in Filter.atTop,
        (2 : ℝ) ^ ((n : ℝ) ^ (3 * δ) - ((min n (m n) : ℕ) : ℝ)) <
            invProb (famHprime O G H lam S m) Astar n →
          (2 : ℝ) ^ ((n : ℝ) ^ (2 * δ) - (m n : ℝ)) ≤
            coinAvg (G.keyLen (lam n) (10 * n) (m n)) (fun k₁ => coinAvg (m n) (fun y =>
              ∑ z : Fin (10 * n) → Bool,
                if (G.circ (lam n) (10 * n) (m n) k₁).eval (List.ofFn z) = bits y then
                  sampA O H Astar (lam n) (S n) n (G.circ (lam n) (10 * n) (m n) k₁) (bits y) (some z)
                else 0))) ∧
      (∀ p : Polynomial ℕ, ∀ᶠ n : ℕ in Filter.atTop, ∀ g g' : MCircuit (10 * n), FunEquiv g g' →
        g.size ≤ p.eval n → g'.size ≤ p.eval n →
        g.size + S₀.eval (lam n + n + m n) ≤ S n → g'.size + S₀.eval (lam n + n + m n) ≤ S n →
        ∀ y : List Bool,
          HybridXorLift.tvDist (sampA O H Astar (lam n) (S n) n g y) (sampA O H Astar (lam n) (S n) n g' y) ≤
            2 ^ (10 * n) * (2 : ℝ) ^ (-((lam n : ℕ) : ℝ) ^ c)) ∧
      (∀ p : Polynomial ℕ, ∀ᶠ n : ℕ in Filter.atTop, ∀ g : MCircuit (10 * n),
        g.size ≤ p.eval n → g.size + S₀.eval (lam n + n + m n) ≤ S n →
        ∀ y : List Bool, (∃ z : Fin (10 * n) → Bool, g.eval (List.ofFn z) = y) →
          HybridXorLift.tvDist (sampA O H Astar (lam n) (S n) n g y)
              (idealDist g y (sampA O H Astar (lam n) (S n) n g y none)) ≤
            2 ^ (10 * n) * (2 : ℝ) ^ (-((lam n : ℕ) : ℝ) ^ c)) := by sorry

end NearOptOWF
