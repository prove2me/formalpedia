-- Prove2me | Theorems.Thm_NoMenuRevenue186_TrustedXOS_proposition_4_6
-- name    : NoMenuRevenue186.TrustedXOS.proposition_4_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:57:39.670472+00:00
-- url     : https://prove2.me/theorems/d2de501f-05c2-4375-9923-99959a81a893
-- title:
--   Proposition 4.6 — uniform no-menu reduction and sublinear-factor consequence
-- statement:
--   Let $\mathcal F,k,\epsilon,K,R$ satisfy the construction assumptions, put $N=|\mathcal F|$, $V=2^K$, and take $\alpha\ge1$. A deterministic ex-post IR, buyer-PIC protocol $\Pi$ may approximate either the deterministic benchmark, or the buy-many benchmark when $\epsilon V<1-\epsilon$. There is one absolute constant $c_0>0$, independent of every parameter and protocol, for which
--
--   $$\mathrm{CC}(\Pi)+1\ge c_0\frac{N\max\{\Delta,0\}^2}{V(K+1)},\qquad
--   \Delta=\frac{1-\epsilon}{\alpha}-\frac2{K+1}.$$
--
--   The statement also retains the consequence for parameter families: for every fixed $\delta>0$ there is $c_\delta>0$ such that, for every sequence of valid constructions and factors $\alpha\ge1$, if eventually $1-\epsilon\ge\delta$ and $\alpha=o(K)$, then eventually every feasible protocol achieving either applicable approximation satisfies
--
--   $$\mathrm{CC}(\Pi)\ge c_\delta\frac{N}{V(K+1)\alpha^2}.$$
--
--   Only the eventual threshold may depend on the parameter family; $c_\delta$ depends on the fixed lower bound $\delta$. The protocol itself is not required to use buy-many prices. This is the communication estimate used in Theorem 3.1.
--
--   Differences from the source:
--   - encoding: absolute Omega in (4.2) and 1-epsilon=Omega(1), alpha=o(K) → one positive c0 before all instances, plus a positive c_delta before all valid parameter sequences with eventual 1-epsilon >= delta and alpha=o(K); reason: explicit uniform constants and epsilon/threshold little-o preserve the two source asymptotic claims, including CC+1 and max(Delta,0)^2
--   - generalization: Section 4.1 starts with a family supplied by Lemma 4.1, whose existence assumptions include epsilon*k >= 2 and k <= epsilon*n/8 → any exact-k separated family satisfying Construction.Valid, without the two existence inequalities; reason: the benchmark, score, and reduction arguments use the supplied family only through separation and the stated size and divisibility conditions; every trimmed source family satisfies these conditions
-- source:
--   Aggarwal, Dang, Rubinstein, Zhao, STOC 2027 submission #186 (October 2026), printed p.18–19, PDF p.20–21, Proposition 4.6 and Equation (4.2)

import Mathlib
import Definitions.Def_NoMenuRevenue186_TrustedXOS_Scores

namespace NoMenuRevenue186.TrustedXOS

/-- Proposition 4.6, printed pp.18–19 (PDF pp.20–21), including both
    applicable benchmarks and its asymptotic consequence. Constants are uniform;
    the eventual threshold in the consequence may depend on the parameter family. -/
theorem proposition_4_6 :
    (∃ c₀ : ℝ, 0 < c₀ ∧ ∀ (n : ℕ) (C : Construction n), C.Valid →
      ∀ α : ℝ, 1 ≤ α → ∀ P : Protocol n, P.Feasible C.instanceLaw → C.Applicable α P →
        c₀ * (C.F.card : ℝ) * max (C.gap α) 0 ^ 2 /
          ((C.V : ℝ) * (C.K + 1 : ℝ)) ≤ (P.cc : ℝ) + 1) ∧
    (∀ δ : ℝ, 0 < δ → ∃ cδ : ℝ, 0 < cδ ∧
      ∀ (ns : ℕ → ℕ) (Cs : (i : ℕ) → Construction (ns i)) (α : ℕ → ℝ),
        (∀ i, (Cs i).Valid ∧ 1 ≤ α i) →
        (∃ M₀ : ℕ, ∀ i ≥ M₀, δ ≤ 1 - (Cs i).ε) →
        LittleO α (fun i => ((Cs i).K : ℝ)) →
        ∃ M : ℕ, ∀ i ≥ M, ∀ P : Protocol (ns i),
          P.Feasible (Cs i).instanceLaw → (Cs i).Applicable (α i) P →
          cδ * ((Cs i).F.card : ℝ) /
            (((Cs i).V : ℝ) * ((Cs i).K + 1 : ℝ) * (α i) ^ 2) ≤ (P.cc : ℝ)) := by sorry

end NoMenuRevenue186.TrustedXOS
