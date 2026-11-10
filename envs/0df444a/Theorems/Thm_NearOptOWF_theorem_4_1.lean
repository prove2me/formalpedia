-- Prove2me | Theorems.Thm_NearOptOWF_theorem_4_1
-- name    : NearOptOWF.theorem_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:50:40.782183+00:00
-- url     : https://prove2.me/theorems/c764eb21-459e-4482-8e7d-c55302ffb3ec
-- title:
--   Theorem 4.1 — subexponential iO and $\mathsf{NP}\not\subseteq_{\mathrm{i.o.}}\mathsf{coAM}$ give $2^{n^\delta-\min\{n,m\}}$-secure one-way functions
-- statement:
--   Assume
--
--   1. $\mathsf{NP} \not\subseteq_{\mathrm{i.o.}} \mathsf{coAM}$, and
--   2. there exists a sub-exponentially secure indistinguishability obfuscator.
--
--   Then for every constant $\delta > 0$ and every polynomially bounded, polynomial-time computable output length $m = m(n)$ there is an efficiently sampleable family $\mathcal H$ of functions $f : \{0,1\}^n \to \{0,1\}^{m(n)}$ such that every PPT algorithm $A$ satisfies, for all sufficiently large $n$,
--   $$
--   \Pr_{f \leftarrow \mathcal H,\ x \leftarrow \{0,1\}^n}\bigl[A(1^n, f, f(x)) = x' \ \wedge\ f(x') = f(x)\bigr] \le 2^{\,n^\delta - \min\{n, m\}} .
--   $$
--
--   The trivial attack that outputs a uniform $x' \in \{0,1\}^n$ succeeds with probability about $2^{-\min\{n,m\}}$, so the bound is optimal up to the factor $2^{n^\delta}$. The paper's family is the padded obfuscation $\mathcal H = \{i\mathcal O(F)\}$ of a puncturable PRF.
--
--   Differences from the source:
--   - reading: "a family of 2^{n^δ−min{n,m}}-secure one-way functions against PPT adversaries" (§3: at most poly(ε) advantage for all large λ) → every PPT inverter's success probability is ≤ 2^{n^δ−min{n,m}} for all sufficiently large n; reason: Theorem 1.3 (p.2) displays the bound this way for m = n; δ is arbitrary, so a poly(n) factor is absorbed
--   - reading: PPT adversaries → uniform machines (published PolyTimeOn) with polynomially many coins, given (1ⁿ, description of f, f(x)); success when the output x′ has length n and f(x′) = f(x); reason: the standard uniform adversary; an inverter can always trim or pad its output to length n
--   - reading: NP ⊄_{i.o.} coAM → some L ∈ NP agrees with no coAM language (published InCoAMPoly: one-round public coin, polynomial resources, errors 1/3) on all inputs of length n for infinitely many n; reason: the standard reading of the infinitely-often inclusion
--   - reading: sub-exponentially secure indistinguishability obfuscator (Definition 3.4, "PPT (resp. polynomial-size) distinguisher", "poly(ε)" advantage) → multi-output circuits, perfect correctness for every coin string, security against non-uniform circuits of size ≤ p(λ) on functionally equivalent pairs of equal size with n ≤ p(λ), advantage ≤ 2^{-λ^δ} for some δ > 0; reason: the proof of Claim 4.7 (p.19) uses the non-uniform variant; equal size is the paper's padding (pp.11–12) and without it no iO exists; ∃δ absorbs poly(ε)
--   - reading: output length m left free ("{0,1}ⁿ → {0,1}ᵐ", "λ = poly(n, m)") → every polynomially bounded, polynomial-time computable m : ℕ → ℕ, universally quantified; the family may depend on δ and m; reason: the theorem is stated for general m; Theorem 1.3 is the case m(n) = n
--   - encoding: a family of one-way functions → a sampler of circuit descriptions with m(n) outputs, polynomial coins and a polynomial-time sampling machine; reason: the efficiently sampleable family of the construction
-- source:
--   Ilango–Lombardi–Tu, Near-Optimal One-Way Functions, Direct Product Hardness and Hash Functions from iO and NP versus coNP, STOC 2027 submission (manuscript of 2026-11-03, sha256 91ede246…), Theorem 4.1, p.11 (PDF p.13)

import Mathlib
import Definitions.Def_NearOptOWF_NPNotSubsetIoCoAM
import Definitions.Def_NearOptOWF_SubexpIOExists
import Definitions.Def_NearOptOWF_FunFamily_IsEfficient
import Definitions.Def_NearOptOWF_Inverter_IsPPT
import Definitions.Def_NearOptOWF_invProb
import Definitions.Def_NearOptOWF_IsPolyLen

namespace NearOptOWF

/-- **Theorem 4.1** (Ilango–Lombardi–Tu, *Near-Optimal One-Way Functions, Direct Product Hardness and Hash Functions from iO and NP versus coNP*, STOC 2027 submission (manuscript of 2026-11-03, sha256 91ede246…), Theorem 4.1, p.11 (PDF p.13)): assume `NP ⊄_{i.o.} coAM` and that a
sub-exponentially secure indistinguishability obfuscator exists. Then for every constant `δ > 0` and
every polynomially bounded, polynomial-time computable output length `m`, there is an efficiently
sampleable family of functions `{0,1}ⁿ → {0,1}^{m(n)}` on which every PPT inverter succeeds with
probability at most `2^{n^δ − min{n, m(n)}}` for all sufficiently large `n`.

**Formalization Note** "`2^{n^δ−min{n,m}}`-secure against PPT adversaries" is read as this bound on
the inversion probability itself (Theorem 1.3, p.2, displays it so for `m = n`); since `δ` is
arbitrary, a `poly(n)` factor would be absorbed. Adversaries are uniform PPT machines given
`(1ⁿ, f, f(x))`. The family may depend on `δ` and `m`. -/
theorem theorem_4_1 (hNP : NPNotSubsetIoCoAM) (hIO : SubexpIOExists) (δ : ℝ) (hδ : 0 < δ)
    (m : ℕ → ℕ) (hm : IsPolyLen m) :
    ∃ H : FunFamily m, H.IsEfficient ∧ ∀ A : Inverter, A.IsPPT → ∀ᶠ n : ℕ in Filter.atTop,
      invProb H A n ≤ (2 : ℝ) ^ ((n : ℝ) ^ δ - ((min n (m n) : ℕ) : ℝ)) := by sorry

end NearOptOWF
