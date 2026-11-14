-- Prove2me | Theorems.Thm_LatticePrepro_ThreeSAT_mem_language_iff
-- name    : LatticePrepro.ThreeSAT.mem_language_iff
-- status  : Proved
-- author  : @WizardOfMenlo
-- created : 2026-11-13T09:25:22.822566+00:00
-- url     : https://prove2.me/theorems/13eb71b9-563c-4157-8a1d-7d1088ffb061
-- title:
--   The 3SAT verifier circuit accepts exactly the satisfiable instances
-- statement:
--   For every number of variables $v$ and every 3SAT instance $x$ on $v$ variables,
--   $$\mathrm{encode}(x) \in L(\mathrm{circuit}_v) \iff x \text{ is satisfiable}.$$
--   Here:
--
--   - $x$ is given by one bit for each of the $(2v)^3$ possible clauses (ordered triples of literals $(i, s)$, with $i$ a variable and $s \in \{0,1\}$ a sign), saying which clauses are present, and $\mathrm{encode}(x) \in \{0,1\}^{(2v)^3}$ lists these bits in a fixed enumeration of the clauses;
--   - $\mathrm{circuit}_v$ is the 3SAT verifier circuit: $(2v)^3$ input wires, $v + 1$ witness wires (an assignment to the $v$ variables and a dummy wire), and $7(2v)^3 + 1$ gates evaluating "every present clause contains a literal satisfied by the assignment";
--   - $L(C)$ is the language of a circuit $C$: the inputs $y$ for which some witness makes the output wire $1$;
--   - $x$ is satisfiable if some assignment $a \in \{0,1\}^v$ satisfies every clause present in $x$, i.e. each present clause has a literal $(i, s)$ with $a_i = s$.
--
--   The proof of Theorem 5.1 takes "$V = V_n$, a verifier for 3SAT"; this theorem establishes that the concrete circuit used in the formalization is such a verifier. Combined with `BoolCircuit.language_toGateVerifier` and Claim 3.15, it yields a quadratic verifier whose language is the set of encodings of satisfiable instances, to which the general results apply (`ThreeSAT.exists_code_gap`, `ThreeSAT.exists_lattice_gap`).
--
--   **Formalization Note**: The statement holds for every $v$, with no lower bound. Polynomial-time constructibility of the circuit is not formalized; the size bound $S \le 9n + 2$ on its number of wires is a separate lemma. The encoding by one bit per possible clause follows the proof of Theorem 5.4 of the paper.
-- source:
--   G. Weissenberg, G. Fenzi, Nearly Optimal Hardness for CVP and NCP with Preprocessing (STOC 2027 submission #847), the verifier $V_n$ for 3SAT in the proof of Theorem 5.1 (\label{thm:approximation-hardness}), with the instance encoding of the proof of Theorem 5.4 (\label{thm:explicit-endpoint}); Lean: LatticePrepro/Verifier/ThreeSAT.lean, LatticePrepro.ThreeSAT.mem_language_iff

import Mathlib
import Definitions.Def_LatticePrepro_Verifier_Quadratic
import Definitions.Def_LatticePrepro_Verifier_Gates
import Definitions.Def_LatticePrepro_Verifier_Circuit
import Definitions.Def_LatticePrepro_Verifier_Expr
import Definitions.Def_LatticePrepro_Verifier_ThreeSAT

open LatticePrepro
open LatticePrepro.ThreeSAT
variable {v : ℕ}

theorem LatticePrepro.ThreeSAT.mem_language_iff (x : Instance v) : encode x ∈ (circuit v).Language ↔ Satisfiable x := by sorry
