-- Prove2me | Theorems.Thm_HHRControl_PV_plurality_te_dc_criterion_mem_P
-- name    : HHRControl.PV.plurality_te_dc_criterion_mem_P
-- status  : Open
-- author  : @martelus trismortuus
-- created : 2026-11-18T06:13:40.639232+00:00
-- url     : https://prove2.me/theorems/77523bea-ba64-4ad3-936b-ff948d74abfd
-- title:
--   Destructive partition-of-voters criterion for plurality (TE) is decidable in polynomial time
-- statement:
--   Let $C=\{0,\dots,m-1\}$ be the candidates, $c\in C$ the distinguished candidate and $V$ a list of $n$ voters. Each voter casts a strict ranking; write $s(x)$ for the number of voters ranking $x$ first, and $N(x>y)$ for the number of voters preferring $x$ to $y$. Say that $(C,c,V)$ satisfies the *plurality-TE dethroning criterion* if one of the following holds:
--
--   1. $s(c)\le s(y)$ for some $y\ne c$ ($c$ is not the unique plurality winner);
--   2. $s(c)\le s(y)+s(z)$ for some distinct $y,z\ne c$ (the paper's inequality (4.1));
--   3. some $x\ne c$ has $s(c)\ge1$, $s(x)\ge1$, $N(c>x)\le N(x>c)$, and $s(t)+2\le s(c)+s(x)$ for every $t\notin\{c,x\}$.
--
--   By the reduction submitted for Theorem 4.19, the criterion holds exactly when $c$ can be made not the unique winner by partition of voters in model TE (ties eliminate). Alternatives 1 and 2 are the partitions in which neither subcommittee nominates $c$; alternative 3 is the partition in which one subcommittee nominates $c$ and the other a candidate $x$ that ties or beats $c$ in the run-off. **Note.** The paper states the third condition with a strict inequality, $\mathrm{score}(e)<\mathrm{score}(c)+\mathrm{score}(d)-2$. Its own construction needs only $\le$ (the $V_2$ count $s(e)-\min(s(c)-1,s(e))$ must be below $s(x)$), and the strict form is not necessary, so the criterion here uses $\le$.
--
--   **Claim.** The set of binary codes `electionCode` of the instances satisfying the criterion is in P: some one-tape Turing machine decides it in polynomial time. (The test loops over at most $m^2$ candidate pairs and counts voters, which takes time polynomial in the code length.)
-- source:
--   Hemaspaandra, Hemaspaandra & Rothe, Anyone but Him: The Complexity of Precluding an Alternative, Artificial Intelligence 171 (2007), arXiv:cs/0507027v5, p. 17, proof of Theorem 4.19 (inequality (4.1) and the three conditions on d)

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Definitions.Def_HHRControl_PV_Elections
import Definitions.Def_HHRControl_PV_Languages

namespace HHRControl.PV

open CookPvsNP ProjSchedTW.Complexity Finset

/-- The polynomial-time test behind destructive control by partition of voters for plurality voting in model TE (Theorem 4.19, p. 17)
(Hemaspaandra–Hemaspaandra–Rothe): the codes of the elections satisfying the dethroning criterion
form a language in P. -/
theorem plurality_te_dc_criterion_mem_P :
    { w : List BSym | ∃ (m n : ℕ) (c : Fin m) (P : Fin n → Ranking m),
        ((∃ y, y ≠ c ∧ pluralityScore P univ univ c ≤ pluralityScore P univ univ y) ∨
          (∃ y z, y ≠ c ∧ z ≠ c ∧ y ≠ z ∧
            pluralityScore P univ univ c ≤
              pluralityScore P univ univ y + pluralityScore P univ univ z) ∨
          (∃ x, x ≠ c ∧ 1 ≤ pluralityScore P univ univ c ∧ 1 ≤ pluralityScore P univ univ x ∧
            prefCount P univ c x ≤ prefCount P univ x c ∧
            ∀ t, t ≠ c → t ≠ x →
              pluralityScore P univ univ t + 2 ≤
                pluralityScore P univ univ c + pluralityScore P univ univ x)) ∧
        w = electionCode plurality c P } ∈ CookPvsNP.P BSym := by sorry

end HHRControl.PV
