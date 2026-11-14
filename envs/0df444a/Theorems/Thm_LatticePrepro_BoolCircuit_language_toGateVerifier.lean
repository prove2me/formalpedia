-- Prove2me | Theorems.Thm_LatticePrepro_BoolCircuit_language_toGateVerifier
-- name    : LatticePrepro.BoolCircuit.language_toGateVerifier
-- status  : Proved
-- author  : @WizardOfMenlo
-- created : 2026-11-13T09:25:43.67501+00:00
-- url     : https://prove2.me/theorems/2c95d1dd-3967-45be-8807-713c1b8e98d6
-- title:
--   Circuits as gate verifiers — ordering the wires as in Definition 3.14 preserves the language
-- statement:
--   Let $C$ be a Boolean circuit with $n$ input wires, $w$ witness wires and $g$ gates in topological order (gate $k$ writes wire $n+w+k$, reads two earlier wires and applies $f_k\colon\{0,1\}^2\to\{0,1\}$), with a designated output gate whose wire is $o$. Let $W_C$ be its gate verifier: the $S = n+w+g$ wires are renumbered in the order "inputs, output wire, remaining wires", and each gate becomes the constraint $z_{\mathrm{out}} = f_k(z_{\mathrm{in}_1}, z_{\mathrm{in}_2})$ on the renumbered wires. Then
--   $$L(W_C) = L(C).$$
--   Explicitly, for every $x \in \{0,1\}^n$ the following are equivalent:
--
--   1. there is a wire assignment $z \in \{0,1\}^S$ satisfying every gate constraint of $W_C$, with $z_i = x_i$ for $i < n$ and $z_n = 1$;
--   2. there is a witness $u \in \{0,1\}^w$ such that the output wire of $C$ evaluates to $1$ on $(x, u)$.
--
--   In the paper, a verifier is a Boolean circuit (Definition 3.13), and its computations are recorded as assignments listing the input bits, the output of the designated gate, the witness bits and the remaining gate outputs (Definition 3.14); the language of $V$ is then the set of $x$ with an accepting computation. This theorem is that correspondence. Together with Claim 3.15 (`GateVerifier.language_toQuadratic`) it turns any Boolean circuit into a quadratic verifier with the same language, for which the main theorems are stated.
--
--   **Formalization Note**: The gate verifier's language is the set of $x$ having a valid wire assignment with prefix $(x, 1)$ (`GateVerifier.Language`); the circuit's language uses the recursive evaluation `evalAux`.
-- source:
--   G. Weissenberg, G. Fenzi, Nearly Optimal Hardness for CVP and NCP with Preprocessing (STOC 2027 submission #847), Definitions 3.13–3.14 (\label{def:verifier}, \label{def:computation-assignment}), where the correspondence is implicit; Lean: LatticePrepro/Verifier/Circuit.lean, LatticePrepro.BoolCircuit.language_toGateVerifier

import Mathlib
import Definitions.Def_LatticePrepro_Verifier_Quadratic
import Definitions.Def_LatticePrepro_Verifier_Gates
import Definitions.Def_LatticePrepro_Verifier_Circuit

open LatticePrepro
open LatticePrepro.BoolCircuit
variable (C : BoolCircuit)

theorem LatticePrepro.BoolCircuit.language_toGateVerifier : C.toGateVerifier.Language = C.Language := by sorry
