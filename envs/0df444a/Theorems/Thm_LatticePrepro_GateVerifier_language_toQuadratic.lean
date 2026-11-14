-- Prove2me | Theorems.Thm_LatticePrepro_GateVerifier_language_toQuadratic
-- name    : LatticePrepro.GateVerifier.language_toQuadratic
-- status  : Proved
-- author  : @WizardOfMenlo
-- created : 2026-11-13T09:25:25.415396+00:00
-- url     : https://prove2.me/theorems/bf635381-264b-44d0-8394-e880961f924a
-- title:
--   Claim 3.15 — quadratic gate equations define the same language as the gates
-- statement:
--   Let $p$ be a prime and $W$ a gate verifier with instance length $n$, wires $0, \dots, S-1$ (inputs $0, \dots, n-1$, output wire $n$) and gates $(o_b, l_b, l'_b, f_b)$ imposing $z_{o_b} = f_b(z_{l_b}, z_{l'_b})$. Let $Q$ be its quadratic verifier over $\mathbb{F}_p$, with coordinates $z_0, \dots, z_S$ (wire $i$ becomes coordinate $i+1$) and gate equations
--   $$Q_b(z) = z_0\, z_{o_b+1} - c_{00}\, z_0^2 - c_{10}\, z_0\, z_{l_b+1} - c_{01}\, z_0\, z_{l'_b+1} - c_{11}\, z_{l_b+1}\, z_{l'_b+1},$$
--   where $c_{00}, c_{10}, c_{01}, c_{11}$ are the coefficients of the multilinear interpolation of $f_b$, reduced mod $p$. Then the two verifiers have the same language:
--   $$L(Q) = L(W).$$
--   That is, for every $x \in \{0,1\}^n$ the following are equivalent:
--
--   1. there is $z \in \mathbb{F}_p^{S+1}$ with $z_0 = 1$, every $z_i \in \{0,1\}$, $Q_b(z) = 0$ for every gate $b$, $z_{i+1} = x_i$ for $i < n$ and $z_{n+1} = 1$ (an accepting assignment of $Q$ on $x$);
--   2. there is a wire assignment in $\{0,1\}^S$ satisfying every gate constraint of $W$, with input $x$ and output wire $1$.
--
--   The main results of the formalization are stated for quadratic verifiers; this theorem (with `BoolCircuit.language_toGateVerifier`) makes them apply to any Boolean circuit, in particular to the 3SAT verifier.
--
--   **Formalization Note**: Claim 3.15 is stated per assignment (a Boolean assignment is valid if and only if all gate equations vanish) and includes the polynomial-time computability of the coefficients; the Lean theorem states the resulting equality of languages, for every prime $p$, and computability is not formalized. Boolean values are identified with $0, 1 \in \mathbb{F}_p$.
-- source:
--   G. Weissenberg, G. Fenzi, Nearly Optimal Hardness for CVP and NCP with Preprocessing (STOC 2027 submission #847), Claim 3.15 (\label{clm:verifier-system}); Lean: LatticePrepro/Verifier/Gates.lean, LatticePrepro.GateVerifier.language_toQuadratic

import Mathlib
import Definitions.Def_LatticePrepro_Verifier_Quadratic
import Definitions.Def_LatticePrepro_Verifier_Gates

open LatticePrepro
open LatticePrepro.GateVerifier
variable (W : GateVerifier)
variable (p : ℕ)
variable [Fact p.Prime]

theorem LatticePrepro.GateVerifier.language_toQuadratic : (W.toQuadratic p).Language = W.Language := by sorry
