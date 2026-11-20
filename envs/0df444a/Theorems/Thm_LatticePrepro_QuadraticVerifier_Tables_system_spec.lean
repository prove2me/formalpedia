-- Prove2me | Theorems.Thm_LatticePrepro_QuadraticVerifier_Tables_system_spec
-- name    : LatticePrepro.QuadraticVerifier.Tables.system_spec
-- status  : Proved
-- author  : @WizardOfMenlo
-- created : 2026-11-20T00:16:17.851823+00:00
-- url     : https://prove2.me/theorems/d44f45a3-d345-4eec-b4d2-fb00b3fbec68
-- title:
--   Theorem 4.8 for the fixed linear system of Construction 4.5 — gap reduction and size bound
-- statement:
--   Let $p$ be a prime and let $V$ be a quadratic verifier over $\mathbb F_p$ with instance length $n$, $S$ assignment coordinates, $N$ evaluation tables and language $L(V)\subseteq\{0,1\}^n$. For a gap exponent $\delta<1$ put $m=\lceil\delta/(1-\delta)\rceil+1$ (`momentAxes`) and $g=(S+1)^{k}$ with $k$ = `gapExp p δ`. **Tables** for $V$ and $\delta$ consist of an integer $B\ge2$ with $8Ng\le B^{m}\le2^{m}\cdot8Ng$ and an explicit moment representation in the sense of Theorem A.8 with $m$ axes and representation bound $r=B^{m}$. They do not depend on the instance.
--
--   The **fixed linear system** of the tables $T$ is the system $Av=b_x$ of Construction 4.5 built from them: $A$ is a fixed $\mathbb F_p$-linear map on $\mathbb F_p^{N_{\mathrm{col}}}$ whose columns are partitioned into $D$ blocks of size $b$, and the right-hand side $b_x$, for $x\in\{0,1\}^n$, is zero except for the entries $\theta_x^{k}$ of the translation equations, where $\theta_x$ is the encoding of the instance.
--
--   **Statement.** Let $\delta<1$ and let $T$ be tables for $V$ and $\delta$. Then the fixed linear system of $T$ satisfies:
--
--   1. **Completeness.** For every $x\in L(V)$, the system $Av=b_x$ has a solution $v\in\{0,1\}^{N_{\mathrm{col}}}$ with at most one nonzero coordinate in each block.
--   2. **Soundness.** For every $x\notin L(V)$, every solution of $Av=b_x$ has Hamming weight more than $g\cdot D$.
--   3. $g<b$ and $D\ge1$.
--   4. **Size.** $N_{\mathrm{col}}^{\,m}\le\bigl(8\,p^{4}\,m\,(S+1)\bigr)^{(m+7)m}\cdot g^{m+1}$.
--
--   This is Theorem 4.8 for the system the paper constructs. The existence form (`exists_gapReduction`) asserts that some linear system family has these properties; here the system is the one of Construction 4.5, and the statement holds for every choice of tables.
--
--   **Formalization Note.** Items 1 and 2 are `IsGapReduction`. The size bound is the bound (22) raised to the $m$-th power. The running-time claims of Theorem 4.8 are not formalized.
-- source:
--   G. Fenzi, G. Weissenberg, Nearly Optimal Hardness for CVP and NCP with Preprocessing (STOC 2027 submission #847; IACR ePrint 2026/2634, https://eprint.iacr.org/2026/2634), Theorem 4.8 (\label{thm:quantitative-affine-gap}) with Construction 4.5 (\label{con:fixed-verifier}) and Theorem 4.6 (\label{thm:fixed-verifier-reduction}); Lean: LatticePrepro/Explicit.lean, LatticePrepro.QuadraticVerifier.Tables.system_spec

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

theorem LatticePrepro.QuadraticVerifier.Tables.system_spec (T : V.Tables δ) (hδ1 : δ < 1) :
    T.system.IsGapReduction V.Language ((V.S + 1) ^ gapExp p δ) ∧
      (V.S + 1) ^ gapExp p δ < T.system.blockSize ∧ 0 < T.system.numBlocks ∧
      Fintype.card T.system.ι ^ momentAxes δ ≤
        (8 * p ^ 4 * momentAxes δ * (V.S + 1)) ^ ((momentAxes δ + 7) * momentAxes δ) *
          ((V.S + 1) ^ gapExp p δ) ^ (momentAxes δ + 1) := by sorry
