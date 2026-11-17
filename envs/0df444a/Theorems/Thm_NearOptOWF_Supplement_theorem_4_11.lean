-- Prove2me | Theorems.Thm_NearOptOWF_Supplement_theorem_4_11
-- name    : NearOptOWF.Supplement.theorem_4_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:13:42.970327+00:00
-- url     : https://prove2.me/theorems/11d4ba03-a32b-48a1-9dea-4d9646789ee8
-- title:
--   Theorem 4.11 — $2^{n^\delta-n}$-secure trapdoor one-way permutations from iO and $\mathsf{NP}\not\subseteq_{\mathrm{i.o.}}\mathsf{coAM}$
-- statement:
--   Assume
--
--   1. $\mathsf{NP}\not\subseteq_{\mathrm{i.o.}}\mathsf{coAM}$, and
--   2. there exists a sub-exponentially secure indistinguishability obfuscator.
--
--   Then for every constant $\delta>0$ there is an efficiently sampleable family $\mathcal P$ of trapdoor permutations of $\{0,1\}^n$ such that every PPT adversary $A$, given the permutation but not the trapdoor, satisfies for all sufficiently large $n$
--   $$
--   \Pr_{P\leftarrow\mathcal P,\ x\leftarrow\{0,1\}^n}\bigl[A(P, P(x))\ \text{outputs}\ x\bigr]\le 2^{n^{\delta}-n}.
--   $$
--
--   Since a random permutation is inverted by a polynomial-time adversary with probability about $\mathrm{poly}(n)\cdot 2^{-n}$, the bound is near-optimal. The theorem upgrades the one-way functions of Theorem 4.1 to trapdoor permutations.
--
--   Differences from the source:
--   - encoding: a family of trapdoor one-way permutations → FunFamily with output length n, IsEfficient, and IsTrapdoorPerm (every sample a bijection of {0,1}^n, a polynomial-time trapdoor from the sampling coins, a polynomial-time inverter using it); reason: the standard definition, matching the construction P = iO(PRP(k,·)) with trapdoor k
--   - reading: 2^{n^δ−n}-secure against PPT adversaries (§3, p.8, where ε-secure means every PPT adversary has at most poly(ε) advantage for all large λ) → every PPT adversary (base Inverter with Inverter.IsPPT, given (1^n, code of P, P(x)) but not the trapdoor) has invProb ≤ 2^{n^δ − n} for all sufficiently large n; reason: the bound ε itself is the stronger reading and is what the proof gives (contrapositive at 2^{n^{3δ}−n}, p.20; δ is arbitrary, so any poly factor is absorbed), as in the base Theorem 4.1; invProb samples x and gives A the image P(x); for a permutation y = P(x) is uniform and the only pre-image is P^{-1}(y), as in the paper's Pr[A*(P,y) = P^{-1}(y)]
--   - encoding: NP ⊄_{i.o.} coAM; a sub-exponentially secure iO → the base predicates NPNotSubsetIoCoAM and SubexpIOExists; reason: the same hypotheses as the base goal Theorem 4.1, read the same way
-- source:
--   Ilango–Lombardi–Tu, Near-Optimal One-Way Functions, Direct Product Hardness and Hash Functions from iO and NP versus coNP, STOC 2027 submission (manuscript of 2026-11-03, sha256 91ede246…), Theorem 4.11 and Eq. (4), p.20 (PDF p.22); proof with Claim 4.12, pp.20–22

import Mathlib
import Definitions.Def_NearOptOWF_NPNotSubsetIoCoAM
import Definitions.Def_NearOptOWF_SubexpIOExists
import Definitions.Def_NearOptOWF_FunFamily_IsEfficient
import Definitions.Def_NearOptOWF_Inverter_IsPPT
import Definitions.Def_NearOptOWF_invProb
import Definitions.Def_NearOptOWF_Supplement_IsTrapdoorPerm

namespace NearOptOWF.Supplement

/-- **Theorem 4.11** (Ilango–Lombardi–Tu, *Near-Optimal One-Way Functions, Direct Product Hardness and Hash Functions from iO and NP versus coNP*, STOC 2027 submission (manuscript of 2026-11-03, sha256 91ede246…), Theorem 4.11, p.20 (PDF p.22)): assume `NP ⊄_{i.o.} coAM` and that a
sub-exponentially secure indistinguishability obfuscator exists. Then for every constant `δ > 0` there is
an efficiently sampleable family of trapdoor permutations of `{0,1}ⁿ` which every PPT inverter, given the
permutation but not the trapdoor, inverts with probability at most `2^{n^δ − n}` for all sufficiently
large `n`.

**Formalization Note** The hypotheses are the base `NPNotSubsetIoCoAM` and `SubexpIOExists`, read as in
the base goal `theorem_4_1`. "`2^{n^δ−n}`-secure" bounds the base inversion probability `invProb`
(`x ← {0,1}ⁿ`, `y = P(x)`, success when the output is a pre-image of `y`), which for a permutation is
`Pr_{P, y←{0,1}ⁿ}[A(P, y) = P⁻¹(y)]` as on p.20. The family may depend on `δ`. -/
theorem theorem_4_11 (hNP : NPNotSubsetIoCoAM) (hIO : SubexpIOExists) (δ : ℝ) (hδ : 0 < δ) :
    ∃ H : FunFamily (fun n => n), H.IsEfficient ∧ IsTrapdoorPerm H ∧
      ∀ A : Inverter, A.IsPPT → ∀ᶠ n : ℕ in Filter.atTop,
        invProb H A n ≤ (2 : ℝ) ^ ((n : ℝ) ^ δ - (n : ℝ)) := by sorry

end NearOptOWF.Supplement
