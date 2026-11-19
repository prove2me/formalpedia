-- Prove2me | Theorems.Thm_HHRControl_PV_approval_te_dc_criterion_mem_P
-- name    : HHRControl.PV.approval_te_dc_criterion_mem_P
-- status  : Open
-- author  : @martelus trismortuus
-- created : 2026-11-18T06:13:34.127425+00:00
-- url     : https://prove2.me/theorems/10ffdd25-0611-4ba2-8e5e-fd7e8b7b2c24
-- title:
--   Destructive partition-of-voters criterion for approval (TE) is decidable in polynomial time
-- statement:
--   Let $C=\{0,\dots,m-1\}$ be the candidates, $c\in C$ the distinguished candidate and $V$ a list of $n$ voters. Each voter casts an approval ballot $A_v\subseteq C$. Say that $(C,c,V)$ satisfies the *approval-TE dethroning criterion* if there are $y,z\ne c$ (possibly equal) with
--
--   $$\#\{v : c\in A_v,\ y\notin A_v,\ z\notin A_v\}\;\le\;\#\{v : c\notin A_v,\ y\in A_v \text{ or } z\in A_v\}.$$
--
--   By the reduction submitted for Theorem 4.21, this holds exactly when $c$ can be made not the unique winner by partition of voters in model TE. The case $y=z$ says that $y$ ties or beats $c$ in total approvals.
--
--   **Claim.** The set of binary codes `electionCode` of the instances satisfying the criterion is in P: some one-tape Turing machine decides it in polynomial time. (The test loops over at most $m^2$ candidate pairs and counts voters, which takes time polynomial in the code length.)
-- source:
--   Hemaspaandra, Hemaspaandra & Rothe, Anyone but Him: The Complexity of Precluding an Alternative, Artificial Intelligence 171 (2007), arXiv:cs/0507027v5, p. 19, proof of Theorem 4.21 (model TE)

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Definitions.Def_HHRControl_PV_Elections
import Definitions.Def_HHRControl_PV_Languages

namespace HHRControl.PV

open CookPvsNP ProjSchedTW.Complexity Finset

/-- The polynomial-time test behind destructive control by partition of voters for approval voting in model TE (Theorem 4.21, p. 19)
(Hemaspaandra–Hemaspaandra–Rothe): the codes of the elections satisfying the dethroning criterion
form a language in P. -/
theorem approval_te_dc_criterion_mem_P :
    { w : List BSym | ∃ (m n : ℕ) (c : Fin m) (P : Fin n → Approval m),
        (∃ y z : Fin m, y ≠ c ∧ z ≠ c ∧
          (univ.filter fun v => c ∈ P v ∧ y ∉ P v ∧ z ∉ P v).card ≤
            (univ.filter fun v => c ∉ P v ∧ (y ∈ P v ∨ z ∈ P v)).card) ∧
        w = electionCode approval c P } ∈ CookPvsNP.P BSym := by sorry

end HHRControl.PV
