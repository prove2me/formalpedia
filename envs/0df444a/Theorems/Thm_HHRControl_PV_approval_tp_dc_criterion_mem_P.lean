-- Prove2me | Theorems.Thm_HHRControl_PV_approval_tp_dc_criterion_mem_P
-- name    : HHRControl.PV.approval_tp_dc_criterion_mem_P
-- status  : Open
-- author  : @martelus trismortuus
-- created : 2026-11-18T06:13:56.152377+00:00
-- url     : https://prove2.me/theorems/bb7adaa6-f8f7-4e27-8b65-87665ed86e15
-- title:
--   Destructive partition-of-voters criterion for approval (TP) is decidable in polynomial time
-- statement:
--   Let $C=\{0,\dots,m-1\}$ be the candidates, $c\in C$ the distinguished candidate and $V$ a list of $n$ voters. Each voter casts an approval ballot $A_v\subseteq C$; write $a(x)$ for the number of voters approving $x$. Say that $(C,c,V)$ satisfies the *approval-TP dethroning criterion* if either $a(c)\le a(x)$ for some $x\ne c$, or there are $y,z\ne c$ with
--
--   $$\#\{v : c\in A_v,\ y,z\notin A_v\}+2\;\le\;\#\{v : c\notin A_v,\ y\in A_v\text{ or }z\in A_v\},$$
--
--   $\#\{v: c\notin A_v,\ y\in A_v\}\ge1$ and $\#\{v: c\notin A_v,\ z\in A_v\}\ge1$.
--
--   By the reduction submitted for Theorem 4.21, this holds exactly when $c$ can be made not the unique winner by partition of voters in model TP (ties promote). The second alternative is a partition in which $y$ strictly beats $c$ in one part and $z$ strictly beats $c$ in the other, so that no subcommittee nominates $c$.
--
--   **Claim.** The set of binary codes `electionCode` of the instances satisfying the criterion is in P: some one-tape Turing machine decides it in polynomial time. (The test loops over at most $m^2$ candidate pairs and counts voters, which takes time polynomial in the code length.)
-- source:
--   Hemaspaandra, Hemaspaandra & Rothe, Anyone but Him: The Complexity of Precluding an Alternative, Artificial Intelligence 171 (2007), arXiv:cs/0507027v5, p. 19 and Appendix A (pp. 34-36), proof of Theorem 4.21 (model TP)

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Definitions.Def_HHRControl_PV_Elections
import Definitions.Def_HHRControl_PV_Languages

namespace HHRControl.PV

open CookPvsNP ProjSchedTW.Complexity Finset

/-- The polynomial-time test behind destructive control by partition of voters for approval voting in model TP (Theorem 4.21, p. 19, corrected in Appendix A, pp. 34–36)
(Hemaspaandra–Hemaspaandra–Rothe): the codes of the elections satisfying the dethroning criterion
form a language in P. -/
theorem approval_tp_dc_criterion_mem_P :
    { w : List BSym | ∃ (m n : ℕ) (c : Fin m) (P : Fin n → Approval m),
        ((∃ x : Fin m, x ≠ c ∧ approvalScore P univ c ≤ approvalScore P univ x) ∨
          ∃ y z : Fin m, y ≠ c ∧ z ≠ c ∧
            (univ.filter fun v => c ∈ P v ∧ y ∉ P v ∧ z ∉ P v).card + 2 ≤
              (univ.filter fun v => c ∉ P v ∧ (y ∈ P v ∨ z ∈ P v)).card ∧
            1 ≤ (univ.filter fun v => c ∉ P v ∧ y ∈ P v).card ∧
            1 ≤ (univ.filter fun v => c ∉ P v ∧ z ∈ P v).card) ∧
        w = electionCode approval c P } ∈ CookPvsNP.P BSym := by sorry

end HHRControl.PV
