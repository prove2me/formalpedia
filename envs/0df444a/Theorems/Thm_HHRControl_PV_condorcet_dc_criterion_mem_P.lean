-- Prove2me | Theorems.Thm_HHRControl_PV_condorcet_dc_criterion_mem_P
-- name    : HHRControl.PV.condorcet_dc_criterion_mem_P
-- status  : Open
-- author  : @martelus trismortuus
-- created : 2026-11-18T05:32:54.936417+00:00
-- url     : https://prove2.me/theorems/a90913f3-057c-4691-b6ea-01176981be28
-- title:
--   Condorcet destructive partition-of-voters criterion is decidable in polynomial time
-- statement:
--   Let $C=\{0,\dots,m-1\}$ be the candidates, $c\in C$ a distinguished candidate and $V$ a list of $n$ voters with strict rankings. Say that $(C,c,V)$ satisfies the *Condorcet dethroning criterion* if there are candidates $d_1,d_2\neq c$ (possibly equal) such that
--
--   $$\#\{v : v \text{ ranks } c \text{ above both } d_1 \text{ and } d_2\} \;\le\; \#\{v : v \text{ ranks } d_1 \text{ or } d_2 \text{ above } c\}.$$
--
--   For $d_1\ne d_2$ this is the paper's inequality (4.2), $W_c - L_c \le S_a + S_b$; taking $d_1=d_2=d$ it says that $c$ does not strictly beat $d$, which covers the paper's trivial case where $c$ is not the Condorcet winner. By the proof of Theorem 4.20, the criterion holds exactly when $c$ can be made not the unique winner by partition of voters (in either tie-handling model).
--
--   **Claim.** The set of binary codes `electionCode` of the instances $(C,c,V)$ satisfying the criterion is in P: some one-tape Turing machine decides it in polynomial time. (The paper's algorithm loops over all pairs $d_1,d_2$ and counts the four voter types, which takes time polynomial in $m$ and $n$.)
-- source:
--   Hemaspaandra, Hemaspaandra & Rothe, Anyone but Him: The Complexity of Precluding an Alternative, Artificial Intelligence 171 (2007), arXiv:cs/0507027v5, p. 18, proof of Theorem 4.20 (stages 1-3 and inequality (4.2))

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Definitions.Def_HHRControl_PV_Elections
import Definitions.Def_HHRControl_PV_Languages

namespace HHRControl.PV

open CookPvsNP ProjSchedTW.Complexity Finset

/-- The polynomial-time test behind Theorem 4.20 (Hemaspaandra–Hemaspaandra–Rothe, p. 18,
inequality (4.2)): the codes of the Condorcet elections `(C, c, V)` for which some `d₁ d₂ ≠ c`
have at most as many voters ranking `c` above both `d₁` and `d₂` as voters ranking `d₁` or `d₂`
above `c` form a language in P. -/
theorem condorcet_dc_criterion_mem_P :
    { w : List BSym | ∃ (m n : ℕ) (c : Fin m) (P : Fin n → Ranking m),
        (∃ d₁ d₂ : Fin m, d₁ ≠ c ∧ d₂ ≠ c ∧
          (univ.filter fun v => P v c < P v d₁ ∧ P v c < P v d₂).card ≤
            (univ.filter fun v => P v d₁ < P v c ∨ P v d₂ < P v c).card) ∧
        w = electionCode condorcet c P } ∈ CookPvsNP.P BSym := by sorry

end HHRControl.PV
