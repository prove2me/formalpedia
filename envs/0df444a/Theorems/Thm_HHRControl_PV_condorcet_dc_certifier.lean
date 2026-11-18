-- Prove2me | Theorems.Thm_HHRControl_PV_condorcet_dc_certifier
-- name    : HHRControl.PV.condorcet_dc_certifier
-- status  : Open
-- author  : @martelus trismortuus
-- created : 2026-11-18T05:32:52.422711+00:00
-- url     : https://prove2.me/theorems/9d67840a-869b-4ef4-a816-080244c7dc04
-- title:
--   Polynomial-time certifier for Condorcet destructive control by partition of voters
-- statement:
--   Let $C=\{0,\dots,m-1\}$ be the candidates, $c\in C$ a distinguished candidate and $V$ a list of $n$ voters with strict rankings. Say that $(C,c,V)$ satisfies the *Condorcet dethroning criterion* if there are candidates $d_1,d_2\neq c$ (possibly equal) such that
--
--   $$\#\{v : v \text{ ranks } c \text{ above both } d_1 \text{ and } d_2\} \;\le\; \#\{v : v \text{ ranks } d_1 \text{ or } d_2 \text{ above } c\}.$$
--
--   For $d_1\ne d_2$ this is the paper's inequality (4.2), $W_c - L_c \le S_a + S_b$; taking $d_1=d_2=d$ it says that $c$ does not strictly beat $d$, which covers the paper's trivial case where $c$ is not the Condorcet winner. By the proof of Theorem 4.20, the criterion holds exactly when $c$ can be made not the unique winner by partition of voters (in either tie-handling model).
--
--   **Claim.** There is a polynomial-time computable function $f$ on instance codes such that: if $(C,c,V)$ satisfies the criterion, then $f$ outputs the code of a partition $(V_1, V\setminus V_1)$ in which $c$ is the Condorcet winner of neither $(C,V_1)$ nor $(C,V\setminus V_1)$; otherwise $f$ outputs the code of "control impossible". (The paper's stage 2 gives such a partition: $V_1$ holds the $S_a$ voters and $\min(W_c,S_a)$ of the $W_c$ voters.)
-- source:
--   Hemaspaandra, Hemaspaandra & Rothe, Anyone but Him: The Complexity of Precluding an Alternative, Artificial Intelligence 171 (2007), arXiv:cs/0507027v5, p. 18, proof of Theorem 4.20 (stages 1-3 and inequality (4.2))

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Definitions.Def_HHRControl_PV_Elections
import Definitions.Def_HHRControl_PV_Languages

namespace HHRControl.PV

open CookPvsNP ProjSchedTW.Complexity Finset

/-- The certifying algorithm behind Theorem 4.20 (Hemaspaandra–Hemaspaandra–Rothe, p. 18): a
polynomial-time function maps the code of every Condorcet election satisfying inequality (4.2) for
some `d₁ d₂ ≠ c` to the code of a partition `(V₁, V₁ᶜ)` in which `c` is the Condorcet winner of
neither part, and every other election code to "control impossible". -/
theorem condorcet_dc_certifier :
    ∃ f : List BSym → List BSym, PolyTimeComputable f ∧
      ∀ (m n : ℕ) (c : Fin m) (P : Fin n → Ranking m),
        ((∃ d₁ d₂ : Fin m, d₁ ≠ c ∧ d₂ ≠ c ∧
            (univ.filter fun v => P v c < P v d₁ ∧ P v c < P v d₂).card ≤
              (univ.filter fun v => P v d₁ < P v c ∨ P v d₂ < P v c).card) →
          ∃ V₁ : Finset (Fin n), c ∉ condorcet.winners m n P univ V₁ ∧
            c ∉ condorcet.winners m n P univ V₁ᶜ ∧
            f (electionCode condorcet c P) = partitionCode V₁) ∧
        (¬ (∃ d₁ d₂ : Fin m, d₁ ≠ c ∧ d₂ ≠ c ∧
            (univ.filter fun v => P v c < P v d₁ ∧ P v c < P v d₂).card ≤
              (univ.filter fun v => P v d₁ < P v c ∨ P v d₂ < P v c).card) →
          f (electionCode condorcet c P) = impossibleCode) := by sorry

end HHRControl.PV
