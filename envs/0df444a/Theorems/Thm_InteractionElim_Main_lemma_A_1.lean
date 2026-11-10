-- Prove2me | Theorems.Thm_InteractionElim_Main_lemma_A_1
-- name    : InteractionElim.Main.lemma_A_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T03:22:29.656931+00:00
-- url     : https://prove2.me/theorems/4a07c5fe-25cc-4d5d-a471-532e740f7b27
-- title:
--   Lemma A.1 — lifted bases $P_j,Q_j$ with $\operatorname{row}Q_j=W_j$, $\sum_j\dim W_j=\operatorname{rank}A$, the kernel identity (A.2), and polynomial-time computability
-- statement:
--   Let $U_j=\operatorname{row}A\cap\{v:v_{>j}=0\}$ and $U_0=0$. For every workflow instance:
--
--   1. for every stage $j$ there are matrices $P_j,Q_j$ whose rows $[P_j,Q_j,0_{>j}]$ extend a basis of $U_{j-1}$ to one of $U_j$, with $Q_j$ of full row rank and $\operatorname{row}Q_j=W_j$;
--   2. (A.1) $\sum_j\dim W_j=\operatorname{rank}A$;
--   3. (A.2) for every $j$,
--   $$
--   W_j^\perp=\operatorname{proj}_{B_j}\big(\ker A\cap\{v:v_{<j}=0\}\big);
--   $$
--   4. all these spaces and lifts are computable by binary linear algebra in polynomial time: there are a constant $C>0$ and one program of the bit-cost machine which, on the explicit input of any instance, halts within $C(N+2)^C$ steps with output listing, for each stage $j$ in order, lifted rows as in item 1 and a basis of $W_j^\perp$.
--
--   The lemma identifies what the expert's record teaches about the current block after a correct prefix ($W_j$) and which current alternatives stay invisible to it ($W_j^\perp$); both directions of the main theorem use it.
--
--   **Formalization Note** The lifted rows are a list of vectors of $\mathbb F_2^R$; $Q_j$ is their restriction to $B_j$ and $P_j$ their part on earlier blocks. "Extend a basis of $U_{j-1}$ to one of $U_j$" is stated as $U_{j-1}+\operatorname{span}(\text{lift})=U_j$ together with independence of the restrictions to $B_j$ (vectors of $U_{j-1}$ vanish on $B_j$). The basis of $W_j^\perp$ is output as vectors of $\mathbb F_2^R$ supported on $B_j$.
--
--   Differences from the source:
--   - encoding: coordinates [R] = {1,…,R}, ordered blocks B_1,…,B_m, x ∈ F_2^R → `Fin R`, a surjective block map `Fin R → Fin m` (0-based stage order), vectors `Fin R → ZMod 2`; reason: index shift only; every ordered partition into nonempty blocks is such a surjection
--   - encoding: matrices P_j, Q_j whose rows [P_j, Q_j, 0_{>j}] extend a basis of U_{j−1} to one of U_j → a list of lifted rows in U_j with U_{j−1} ⊔ span(list) = U_j and linearly independent restrictions to B_j spanning W_j; reason: the same data: P_j and Q_j are the parts of the rows before and inside B_j, and vectors of U_{j−1} vanish on B_j
--   - reading: 'All these spaces and lifts are computable by binary linear algebra in polynomial time' → one program of the bit-cost machine, fixed before the instance, outputs on the explicit input (for every coin tape) lifts for every stage and a basis of every W_j^⊥ within C·(N+2)^C steps; reason: polynomial time in the bit length N of the explicit input; U_j and W_j are spanned by the output lifts
-- source:
--   Jin, Zang, Xu, Li, Eliminating Ongoing Interaction in Long-Running Verification Agents, STOC 2027 submission (manuscript sha256 44f6d829…), p. 17, Lemma A.1

import Mathlib
import Definitions.Def_InteractionElim_Main_Machine

open scoped BigOperators ENNReal
open MeasureTheory Matrix

namespace InteractionElim.Main

theorem lemma_A_1 :
    (∀ (I : Instance) (j : Fin I.m), ∃ lift : List (Fin I.R → ZMod 2), I.IsLift j lift) ∧
    (∀ I : Instance, ∑ j, Module.finrank (ZMod 2) (I.W j) = I.A.rank) ∧
    (∀ (I : Instance) (j : Fin I.m),
      orth (I.W j) = (I.kerA ⊓ I.earlierZero j).map (I.restrict j)) ∧
    ∃ C : ℝ, 0 < C ∧ ∃ prog : Program, ∀ (I : Instance) (ρ : Tape),
      ∃ lifts perps : Fin I.m → List (Fin I.R → ZMod 2),
        (∀ j, I.IsLift j (lifts j) ∧ I.IsPerpBasis j (perps j)) ∧
        progOut prog (encInstance I) ρ =
          some (List.ofFn fun j => encList encVec (lifts j) ++ encList encVec (perps j)).flatten ∧
        progTime prog (encInstance I) ρ ≤ ENNReal.ofReal (C * ((I.N : ℝ) + 2) ^ C) := by sorry

end InteractionElim.Main
