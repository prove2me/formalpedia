-- Prove2me | Theorems.Thm_IsRandomnessNecessaryADA_Plain_Supplement_theorem_1_4
-- name    : IsRandomnessNecessaryADA.Plain.Supplement.theorem_1_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-15T17:23:37.608544+00:00
-- url     : https://prove2.me/theorems/8eabc546-b813-485e-9672-9e5a580d7036
-- title:
--   Theorem 1.4 — limited private randomness
-- statement:
--   There are absolute constants $C_X,C_k>0$ such that for every sample size $n>2$ and every integer bit budget $b\ge0$, there exist positive integers $d,k$, fixed before the mechanism, satisfying
--
--   $$d\le2^{C_X(n^2\log_2 n+nb)},\qquad k\le C_k(n\log_2 n+b).$$
--
--   For every unrestricted mechanism on $X=\{0,\ldots,d-1\}$ using at most $b$ independent fair private bits in total, there are an injection $e:[20n]\hookrightarrow X$ and one history-only Boolean-query analyst $A$. Let $P$ be uniform on the $20n$ distinct image points, draw the ordered sample $S\sim P^n$ with replacement, and independently draw one uniform private tape $\sigma\in\{0,1\}^b$ for the mechanism. Run the $k$-round interaction with the same tape throughout. Then
--
--   $$\Pr_{S,\sigma}\!\left[\exists j\in\{1,\ldots,k\}:\left|a_j-\mathbb E_{x\sim P}q_j(x)\right|>\frac1{10}\right]\ge\frac9{10}.$$
--
--   The distribution and analyst may depend on the mechanism but are chosen before its realized sample and tape. The analyst sees only the real transcript and issues Boolean queries; the mechanism sees full query functions and may return arbitrary real answers. No naturalness, computational bound, distribution input to the mechanism, or sample/seed input to the analyst is imposed. This is the paper's companion randomness-budget lower bound, independent of its deterministic goal. Its mathematical proof is in the source; the staged Lean theorem is an unproved formalization target.
--
--   **Formalization Note** A mechanism is a family of deterministic full-query response functions indexed by a persistent $b$-bit tape. Unused tape bits encode mechanisms consuming fewer bits, including adaptive consumption. A single deterministic analyst can be fixed by averaging independent analyst coins after the fixed distribution is chosen, without fixing or revealing the mechanism tape. The proof's explicit seed-aware $k,M,d$ are staged separately as computed witnesses; their asymptotic estimates remain proof obligations. The strict error comes from Theorem 1.4 on p.3, rather than the non-strict recap on p.15.
--
--   Differences from the source:
--   - encoding: finite domains and nonnegative integer bit budgets, asymptotic query and domain bounds → Fin d, b : ℕ, base-two logarithms and absolute positive real constants quantified before n and b; reason: finite reindexing and a change of logarithm base preserve every source instance and both uniform asymptotic bounds
--   - encoding: a computationally unbounded analyst, with private attack randomness permitted → one deterministic Boolean history-only analyst, with probability over the independent sample and persistent uniform mechanism seed; reason: the proof gives joint success at least 199/200; averaging fixes hidden locations and independent analyst coins while retaining success at least 9/10 over sample and every mechanism seed
--   - encoding: a mechanism using at most b private random bits → a family σ ↦ m_σ of unrestricted deterministic mechanisms indexed by σ : Fin b → Bool, with σ drawn once, uniformly and independently of the sample, and kept for all k rounds; reason: any mechanism consuming at most b fair coins, possibly adaptively or fewer, is such a family (unused coordinates ignored), and every such family uses at most b fair coins
-- source:
--   Edith Cohen, Haim Kaplan, Yishay Mansour, Shay Sapir, Uri Stemmer, Eliad Tsfadia, Is Randomness Necessary for Adaptive Data Analysis?, STOC 2027 submission #267 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/267.pdf, Theorem 1.4, p.3 (PDF p.3); proof §4.5, p.15 (PDF p.15), Definitions 2.1–2.2, pp.7–8.

import Definitions.Def_IsRandomnessNecessaryADA_Plain_Supplement_SeedProtocol

set_option autoImplicit false

namespace IsRandomnessNecessaryADA.Plain.Supplement

/-- Theorem 1.4, p.3, full strength; Section 4.5, p.15.
Absolute constants precede n,b; domain/horizon precede the mechanism.
The fixed distribution and single analyst precede both the sample and private tape. -/
theorem theorem_1_4 :
    ∃ C_X C_k : ℝ, 0 < C_X ∧ 0 < C_k ∧
      ∀ (n : ℕ) (hn : 2 < n) (b : ℕ), ∃ d k : ℕ,
        0 < d ∧ 0 < k ∧
        (d : ℝ) ≤ (2 : ℝ) ^
          (C_X * ((n : ℝ) ^ 2 * (Real.log n / Real.log 2) + (n : ℝ) * b)) ∧
        (k : ℝ) ≤ C_k * ((n : ℝ) * (Real.log n / Real.log 2) + b) ∧
        ∀ m : SeedMechanism (Fin d) n b,
          ∃ (e : Fin (20 * n) ↪ Fin d) (A : BooleanAnalyst (Fin d)),
            (9 / 10 : ℝ) ≤
              probability (seedInteractionLaw m (liftAnalyst A)
                (uniformSupport (by omega) e) k)
                (errorEvent (uniformSupport (by omega) e) (1 / 10)) := by sorry

end IsRandomnessNecessaryADA.Plain.Supplement
