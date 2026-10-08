-- Prove2me | Theorems.Thm_ObfImpossibility_PseudoOracle_chernoff_count_T
-- name    : ObfImpossibility.PseudoOracle.chernoff_count_T
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T10:29:37.612206+00:00
-- url     : https://prove2.me/theorems/83855b3f-7381-4ae8-922a-6ccafbd74cb7
-- title:
--   Proof of Claim B.1.2, p. A:45 — at most an $\exp(-c\,m\varepsilon^2)$ fraction of $m$-subsets $T$ overestimate a Boolean average by $\varepsilon$
-- statement:
--   There is an absolute constant $c>0$ with the following property. Let $U$ be a finite set, $f:U\to\{0,1\}$, $m\in\mathbb N$ and $\varepsilon>0$. Then the number of $m$-element subsets $T\subseteq U$ with
--   $$\Pr_{y\in T}\big[f(y)=1\big]-\Pr_{y\in U}\big[f(y)=1\big]>\varepsilon$$
--   is at most $\exp(-c\,m\,\varepsilon^2)\binom{|U|}{m}$.
--
--   This is the Chernoff bound for sampling without replacement that the paper invokes ("most large subsets are good approximators of the average of a Boolean function"). Applied with $U=L_G$, $f=M$, $m=|S_G|\approx(1-\gamma)K^{1-5\delta}$ and $\varepsilon=\frac1{2K^\delta}$, it says that at most an $\exp(-\Omega(K^{1-7\delta}))$ fraction of the possible images $T=G(S_G)$ satisfy inequality (9), which is the saving in the description of $G$.
--
--   **Formalization Note** The constant $c$ is quantified before the type $U$ lives in, so it is universal. For $m=0$ the empty set has average $0$ and the count is $0$; for $m>|U|$ both sides are $0$.
-- source:
--   Barak et al., On the (Im)possibility of Obfuscating Programs, J. ACM 59(2) (2012), author's copy, p. A:45, Appendix B, proof of Claim B.1.2 (Chernoff bound for the sets T satisfying (9))

import Mathlib
import Definitions.Def_ObfImpossibility_PseudoOracle_Setting

namespace ObfImpossibility.PseudoOracle

/-- The Chernoff count, p. A:45 (proof of Claim B.1.2): there is an absolute constant
`c > 0` such that for every Boolean function `f` on a finite set `U`, every `m` and every
`ε > 0`, at most an `exp(-c m ε²)` fraction of the `m`-element subsets `T ⊆ U` satisfy
`Pr_{y∈T}[f(y) = 1] - Pr_{y∈U}[f(y) = 1] > ε`. -/
theorem chernoff_count_T :
    ∃ c : ℝ, 0 < c ∧ ∀ {α : Type} [DecidableEq α] (U : Finset α) (f : α → Bool) (m : ℕ)
      (ε : ℝ), 0 < ε →
        (((U.powersetCard m).filter fun T => ε < avg T f - avg U f).card : ℝ) ≤
          Real.exp (-(c * (m : ℝ) * ε ^ 2)) * ((U.card.choose m : ℕ) : ℝ) := by sorry

end ObfImpossibility.PseudoOracle
