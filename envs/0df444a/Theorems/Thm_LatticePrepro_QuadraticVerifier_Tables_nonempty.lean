-- Prove2me | Theorems.Thm_LatticePrepro_QuadraticVerifier_Tables_nonempty
-- name    : LatticePrepro.QuadraticVerifier.Tables.nonempty
-- status  : Proved
-- author  : @WizardOfMenlo
-- created : 2026-11-20T00:16:07.594915+00:00
-- url     : https://prove2.me/theorems/73f21045-ef7a-46d0-943e-ded715ac696d
-- title:
--   Theorem 4.8 (choice of parameters) and Theorem A.8 — tables exist for every verifier
-- statement:
--   Let $p$ be a prime and let $V$ be a quadratic verifier over $\mathbb F_p$ with instance length $n$, $S$ assignment coordinates, $N$ evaluation tables and language $L(V)\subseteq\{0,1\}^n$. For a gap exponent $\delta<1$ put $m=\lceil\delta/(1-\delta)\rceil+1$ (`momentAxes`) and $g=(S+1)^{k}$ with $k$ = `gapExp p δ`. **Tables** for $V$ and $\delta$ consist of an integer $B\ge2$ with $8Ng\le B^{m}\le2^{m}\cdot8Ng$ and an explicit moment representation in the sense of Theorem A.8 with $m$ axes and representation bound $r=B^{m}$. They do not depend on the instance.
--
--   **Statement.** If $S\ge2$ and $\delta<1$, then tables for $V$ and $\delta$ exist.
--
--   The base $B$ is the one chosen in the proof of Theorem 4.8 (the least $B\ge2$ with $B^{m}\ge8Ng$), and the moment representation is the one of Theorem A.8 for the parameters $S$, $m$ and $B$.
--
--   **Formalization Note.** The conclusion is `Nonempty (V.Tables δ)`. The hypothesis $S\ge2$ is the one of Theorem A.8; it holds for the 3SAT verifier.
-- source:
--   G. Fenzi, G. Weissenberg, Nearly Optimal Hardness for CVP and NCP with Preprocessing (STOC 2027 submission #847; IACR ePrint 2026/2634, https://eprint.iacr.org/2026/2634), proof of Theorem 4.8 (\label{thm:quantitative-affine-gap}), choice of the base, and Theorem A.8 (\label{thm:moment-representation-construction}); Lean: LatticePrepro/Explicit.lean, LatticePrepro.QuadraticVerifier.Tables.nonempty

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

theorem LatticePrepro.QuadraticVerifier.Tables.nonempty (V : QuadraticVerifier p) (hS : 2 ≤ V.S) {δ : ℝ} (hδ1 : δ < 1) :
    Nonempty (V.Tables δ) := by sorry
