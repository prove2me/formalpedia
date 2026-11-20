-- Prove2me | Theorems.Thm_LatticePrepro_QuadraticVerifier_Tables_codeFamily_hasGap
-- name    : LatticePrepro.QuadraticVerifier.Tables.codeFamily_hasGap
-- status  : Proved
-- author  : @WizardOfMenlo
-- created : 2026-11-20T00:15:46.905716+00:00
-- url     : https://prove2.me/theorems/16c29f9e-f754-422b-ad08-5867ec01dcb5
-- title:
--   Theorem 5.1 (codes) for the paper's code — the code $\ker A\times\{0\}$ of the fixed linear system has gap $M^{1-\varepsilon}$
-- statement:
--   Let $p$ be a prime and let $V$ be a quadratic verifier over $\mathbb F_p$ with instance length $n$, $S$ assignment coordinates, $N$ evaluation tables and language $L(V)\subseteq\{0,1\}^n$. For a gap exponent $\delta<1$ put $m=\lceil\delta/(1-\delta)\rceil+1$ (`momentAxes`) and $g=(S+1)^{k}$ with $k$ = `gapExp p δ`. **Tables** for $V$ and $\delta$ consist of an integer $B\ge2$ with $8Ng\le B^{m}\le2^{m}\cdot8Ng$ and an explicit moment representation in the sense of Theorem A.8 with $m$ axes and representation bound $r=B^{m}$. They do not depend on the instance.
--
--   The **fixed linear system** of the tables $T$ is the system $Av=b_x$ of Construction 4.5 built from them: $A$ is a fixed $\mathbb F_p$-linear map on $\mathbb F_p^{N_{\mathrm{col}}}$ whose columns are partitioned into $D$ blocks of size $b$, and the right-hand side $b_x$, for $x\in\{0,1\}^n$, is zero except for the entries $\theta_x^{k}$ of the translation equations, where $\theta_x$ is the encoding of the instance.
--
--   **Statement.** Let $F$ be a field of characteristic $p$, let $0<\varepsilon<1$, and let $T$ be tables for $V$ and $\delta=1-\varepsilon$. Let $\mathcal C\subseteq F^{M}$, $M=2N_{\mathrm{col}}$, be the code spanned over $F$ by $\ker A\times\{0\}$, with the targets $t_x=(v_x,0)$ for a solution $v_x$ of $Av=b_x$ if there is one and $t_x=(0,\mathbf 1)$ otherwise. Then, with $C$ = `sizeExp p (1 - ε)`,
--   $$1\le M\le(S+1)^{C},\qquad D\ge1,$$
--   $$x\in L(V)\ \Longrightarrow\ \Delta(t_x,\mathcal C)\le D,\qquad x\notin L(V)\ \Longrightarrow\ \Delta(t_x,\mathcal C)>M^{1-\varepsilon}\cdot D .$$
--
--   This is Theorem 5.1 for codes, for an arbitrary quadratic verifier, with the radius $R=D$. The existence form of this statement only asserts that some code or lattice with targets has the gap. Since the Lean statement does not require the targets to be computable, that form is satisfied by a construction unrelated to the paper, in which the target records whether $x$ is in the language. Here the code, the lattice and the targets are the ones the paper constructs.
--
--   **Formalization Note.** The statement holds for every choice of tables; they exist by `Tables.nonempty`. The conclusion is `CodeFamily.HasGap`. The field $F$ is any field that is an $\mathbb F_p$-algebra (the paper takes it finite). Polynomial-time computability of the code, the lattice and the targets is not formalized. The target uses a solution of $Av=b_x$ picked by classical choice, where the paper uses Gaussian elimination; the distance from the target to the code does not depend on the solution.
-- source:
--   G. Fenzi, G. Weissenberg, Nearly Optimal Hardness for CVP and NCP with Preprocessing (STOC 2027 submission #847; IACR ePrint 2026/2634, https://eprint.iacr.org/2026/2634), Theorem 5.1 (\label{thm:approximation-hardness}), code case, with Lemma 3.11 (\label{lem:block-system-codes}) and Construction 4.5 (\label{con:fixed-verifier}); Lean: LatticePrepro/Explicit.lean, LatticePrepro.QuadraticVerifier.Tables.codeFamily_hasGap

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

theorem LatticePrepro.QuadraticVerifier.Tables.codeFamily_hasGap (F : Type) [Field F] [DecidableEq F] [Algebra (ZMod p) F] {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε < 1) (T : V.Tables (1 - ε)) :
    (T.codeFamily F).HasGap T.system.numBlocks ε V.Language (V.S + 1) (sizeExp p (1 - ε)) := by sorry
