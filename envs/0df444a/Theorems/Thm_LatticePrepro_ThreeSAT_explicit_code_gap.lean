-- Prove2me | Theorems.Thm_LatticePrepro_ThreeSAT_explicit_code_gap
-- name    : LatticePrepro.ThreeSAT.explicit_code_gap
-- status  : Proved
-- author  : @WizardOfMenlo
-- created : 2026-11-20T00:16:06.194792+00:00
-- url     : https://prove2.me/theorems/58beeb39-cf83-4054-a953-499f8e3d5761
-- title:
--   Theorem 5.1 (codes, 3SAT) for the paper's code — gap $M^{1-\varepsilon}$ with $M\le n^{C}$
-- statement:
--   Instances of 3SAT on $v$ variables are encoded as bit strings of length $n=(2v)^{3}$, one bit per possible clause, and $V_v$ is the quadratic verifier of the 3SAT verifier circuit over the relevant prime field. Tables for $V_v$ consist of a base and an explicit moment representation (Theorem A.8) in the ranges of the proof of Theorem 4.8; they do not depend on the instance.
--
--   **Codes.** For every prime $p$, every finite field $F$ of characteristic $p$ and every $0<\varepsilon<1$, there is $C\in\mathbb N$ such that for every $v\ge1$ there are tables $T$ for $V_v$ over $\mathbb F_p$ for which the following holds. Let $Av=b_x$ be the fixed linear system of Construction 4.5 for $T$, with $D$ blocks, and let $\mathcal C\subseteq F^{M}$ be the code spanned over $F$ by $\ker A\times\{0\}$, with the targets $t_x$ of Lemma 3.11. Then $1\le M\le n^{C}$, $D\ge1$, and
--   $$x\ \text{satisfiable}\ \Longrightarrow\ \Delta(t_x,\mathcal C)\le D,\qquad x\ \text{unsatisfiable}\ \Longrightarrow\ \Delta(t_x,\mathcal C)>M^{1-\varepsilon}\cdot D .$$
--
--   This is the code half of Theorem 5.1 for the code that the paper constructs. The existence form of this statement only asserts that some code or lattice with targets has the gap. Since the Lean statement does not require the targets to be computable, that form is satisfied by a construction unrelated to the paper, in which the target records whether $x$ is in the language. Here the code, the lattice and the targets are the ones the paper constructs.
--
--   **Formalization Note.** Only the tables are asserted to exist; the code, the lattice, the targets and the radius are defined from them, and the instance enters through the right-hand side $b_x$ of the fixed linear system alone. Polynomial-time computability of the code, the lattice and the targets is not formalized. The target uses a solution of $Av=b_x$ picked by classical choice, where the paper uses Gaussian elimination; the distance from the target to the code does not depend on the solution. The description lengths of Theorem 5.1 are not formalized either.
-- source:
--   G. Fenzi, G. Weissenberg, Nearly Optimal Hardness for CVP and NCP with Preprocessing (STOC 2027 submission #847; IACR ePrint 2026/2634, https://eprint.iacr.org/2026/2634), Theorem 5.1 (\label{thm:approximation-hardness}), codes, for the 3SAT verifier; Lean: LatticePrepro/Explicit.lean, LatticePrepro.ThreeSAT.explicit_code_gap

import Mathlib
import Definitions.Def_LatticePrepro_Basic_Blocks
import Definitions.Def_LatticePrepro_Reduction_LinearSystem
import Definitions.Def_LatticePrepro_Conversions_Codes
import Definitions.Def_LatticePrepro_Conversions_Codes_Ext
import Definitions.Def_LatticePrepro_Conversions_ConstructionA
import Definitions.Def_LatticePrepro_Conversions_ConstructionA_Ext
import Definitions.Def_LatticePrepro_Conversions_Hadamard
import Definitions.Def_LatticePrepro_Conversions_Hadamard_Ext
import Definitions.Def_LatticePrepro_Conversions_Padding
import Definitions.Def_LatticePrepro_Conversions_Lattices
import Definitions.Def_LatticePrepro_Conversions_Lattices_Ext
import Definitions.Def_LatticePrepro_Lattices_Distance
import Definitions.Def_LatticePrepro_Moments_Basic
import Definitions.Def_LatticePrepro_Moments_Representation
import Definitions.Def_LatticePrepro_Verifier_Quadratic
import Definitions.Def_LatticePrepro_Reduction_FixedSystem
import Definitions.Def_LatticePrepro_Tables_Digits
import Definitions.Def_LatticePrepro_Tables_FieldSetup
import Definitions.Def_LatticePrepro_Tables_Hankel
import Definitions.Def_LatticePrepro_Tables_Construction
import Definitions.Def_LatticePrepro_Tables_ElementTable
import Definitions.Def_LatticePrepro_Tables_TableSoundness
import Definitions.Def_LatticePrepro_Tables_Explicit
import Definitions.Def_LatticePrepro_Lattices_Mathlib
import Definitions.Def_LatticePrepro_Main
import Definitions.Def_LatticePrepro_Verifier_Gates
import Definitions.Def_LatticePrepro_Verifier_Circuit
import Definitions.Def_LatticePrepro_Verifier_Expr
import Definitions.Def_LatticePrepro_Verifier_ThreeSAT
import Definitions.Def_LatticePrepro_ThreeSAT
import Definitions.Def_LatticePrepro_ThreeSAT_Ext
import Definitions.Def_LatticePrepro_Explicit

open LatticePrepro
open LatticePrepro.ThreeSAT
open QuadraticVerifier

theorem LatticePrepro.ThreeSAT.explicit_code_gap (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Fintype F]
    [DecidableEq F] [Algebra (ZMod p) F] (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ C : ℕ, ∀ v : ℕ, 1 ≤ v → ∃ T : (verifier p v).Tables (1 - ε),
      ((T.codeFamily F).comap encode).HasGap T.system.numBlocks ε (SAT v) (len v) C := by sorry
