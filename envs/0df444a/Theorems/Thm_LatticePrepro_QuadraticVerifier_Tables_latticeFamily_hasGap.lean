-- Prove2me | Theorems.Thm_LatticePrepro_QuadraticVerifier_Tables_latticeFamily_hasGap
-- name    : LatticePrepro.QuadraticVerifier.Tables.latticeFamily_hasGap
-- status  : Proved
-- author  : @WizardOfMenlo
-- created : 2026-11-20T00:16:18.823656+00:00
-- url     : https://prove2.me/theorems/6d47604b-8fd3-47e8-938f-b4afd2542da4
-- title:
--   Theorem 5.1 (lattices) for the paper's lattice — the lattice of Lemma 3.12 for the fixed linear system has gap $M^{1/s-\varepsilon}$
-- statement:
--   Let $p'\ge1$ be a real norm exponent or $p'=\infty$, with $s=\min\{p',2\}$, and let $0<\varepsilon<1/s$. Let $V$ be a quadratic verifier over $\mathbb F_2$ with instance length $n$, $S$ assignment coordinates and language $L(V)$, and let $T$ be tables for $V$ and the gap exponent $\delta=1-s\varepsilon$ (a base and an explicit moment representation, independent of the instance). Let $Av=b_x$ be the fixed linear system of Construction 4.5 for $T$, with $D$ blocks, let $\Lambda\subseteq\mathbb Z^{M}$ be the lattice of Lemma 3.12 for this system (the Construction A lattice of the padded code $\ker A\times\{0\}$ if $p'\le2$, its blockwise Walsh–Hadamard transform otherwise), with its integer targets $t_x$, and let $R$ be the radius of Lemma 3.12 ($\lceil D^{1/p'}\rceil$, $\lceil(2^{k}D)^{1/p'}\rceil$ or $1$).
--
--   **Statement.** With $C$ = `sizeExp 2 (1 - s ε)`,
--   $$1\le M\le(S+1)^{C},\qquad R\ge1,\qquad N\cdot\mathbb Z^{M}\subseteq\Lambda\ \text{for some integer }N>0,$$
--   $$x\in L(V)\ \Longrightarrow\ \operatorname{dist}_{p'}(t_x,\Lambda)\le R,\qquad x\notin L(V)\ \Longrightarrow\ \operatorname{dist}_{p'}(t_x,\Lambda)>M^{1/s-\varepsilon}\cdot R .$$
--
--   This is Theorem 5.1 for lattices, for an arbitrary quadratic verifier over $\mathbb F_2$. The existence form of this statement only asserts that some code or lattice with targets has the gap. Since the Lean statement does not require the targets to be computable, that form is satisfied by a construction unrelated to the paper, in which the target records whether $x$ is in the language. Here the code, the lattice and the targets are the ones the paper constructs.
--
--   **Formalization Note.** The statement holds for every choice of tables; they exist by `Tables.nonempty`. The conclusion is `LatticeFamily.HasGap`. The exponent $p'$ ranges over all reals $p'\ge1$ and $\infty$ (the paper takes $p'$ rational). Polynomial-time computability of the lattice and the targets is not formalized. The target uses a solution of $Av=b_x$ picked by classical choice, where the paper uses Gaussian elimination; the distance from the target to the lattice does not depend on the solution.
-- source:
--   G. Fenzi, G. Weissenberg, Nearly Optimal Hardness for CVP and NCP with Preprocessing (STOC 2027 submission #847; IACR ePrint 2026/2634, https://eprint.iacr.org/2026/2634), Theorem 5.1 (\label{thm:approximation-hardness}), lattice case, with Lemma 3.12 (\label{lem:block-system-lattices}) and Construction 4.5 (\label{con:fixed-verifier}); Lean: LatticePrepro/Explicit.lean, LatticePrepro.QuadraticVerifier.Tables.latticeFamily_hasGap

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
open LatticePrepro.QuadraticVerifier
variable {p : ℕ} [hp : Fact p.Prime]
open LatticePrepro.QuadraticVerifier.Tables
variable {V : QuadraticVerifier p} {δ : ℝ}

theorem LatticePrepro.QuadraticVerifier.Tables.latticeFamily_hasGap (pn : PNorm) {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1 / pn.s)
    {V : QuadraticVerifier 2} (T : V.Tables (1 - pn.s * ε)) :
    (T.latticeFamily pn).HasGap pn (T.latticeRadius pn) ε V.Language (V.S + 1)
      (sizeExp 2 (1 - pn.s * ε)) := by sorry
