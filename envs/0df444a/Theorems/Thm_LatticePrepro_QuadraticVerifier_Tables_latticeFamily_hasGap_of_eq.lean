-- Prove2me | Theorems.Thm_LatticePrepro_QuadraticVerifier_Tables_latticeFamily_hasGap_of_eq
-- name    : LatticePrepro.QuadraticVerifier.Tables.latticeFamily_hasGap_of_eq
-- status  : Proved
-- author  : @WizardOfMenlo
-- created : 2026-11-20T00:15:30.131193+00:00
-- url     : https://prove2.me/theorems/56e8ea2e-83ef-43da-830a-be1bd4d05fab
-- title:
--   Theorem 5.1 (lattices) for the paper's lattice, with the gap exponent $\delta=1-s\varepsilon$ as a variable
-- statement:
--   Let $p'\ge1$ be a real norm exponent or $p'=\infty$, with $s=\min\{p',2\}$, and let $0<\varepsilon<1/s$. Let $V$ be a quadratic verifier over $\mathbb F_2$ with instance length $n$, $S$ assignment coordinates and language $L(V)$, and let $T$ be tables for $V$ and a real number $\delta$ with $\delta=1-s\varepsilon$ (a base and an explicit moment representation, independent of the instance). Let $Av=b_x$ be the fixed linear system of Construction 4.5 for $T$, with $D$ blocks, let $\Lambda\subseteq\mathbb Z^{M}$ be the lattice of Lemma 3.12 for this system (the Construction A lattice of the padded code $\ker A\times\{0\}$ if $p'\le2$, its blockwise Walsh–Hadamard transform otherwise), with its integer targets $t_x$, and let $R$ be the radius of Lemma 3.12 ($\lceil D^{1/p'}\rceil$, $\lceil(2^{k}D)^{1/p'}\rceil$ or $1$).
--
--   **Statement.** With $C$ = `sizeExp 2 δ`,
--   $$1\le M\le(S+1)^{C},\qquad R\ge1,\qquad N\cdot\mathbb Z^{M}\subseteq\Lambda\ \text{for some integer }N>0,$$
--   $$x\in L(V)\ \Longrightarrow\ \operatorname{dist}_{p'}(t_x,\Lambda)\le R,\qquad x\notin L(V)\ \Longrightarrow\ \operatorname{dist}_{p'}(t_x,\Lambda)>M^{1/s-\varepsilon}\cdot R .$$
--
--   This is the statement `Tables.latticeFamily_hasGap` with the exponent $\delta$ kept as a variable that is assumed equal to $1-s\varepsilon$. It carries the proof; the stated form of Theorem 5.1 for lattices follows by substituting $\delta$.
--
--   **Formalization Note.** The conclusion is `LatticeFamily.HasGap`. Polynomial-time computability of the lattice and the targets is not formalized. The target uses a solution of $Av=b_x$ picked by classical choice, where the paper uses Gaussian elimination; the distance from the target to the lattice does not depend on the solution.
-- source:
--   G. Fenzi, G. Weissenberg, Nearly Optimal Hardness for CVP and NCP with Preprocessing (STOC 2027 submission #847; IACR ePrint 2026/2634, https://eprint.iacr.org/2026/2634), Theorem 5.1 (\label{thm:approximation-hardness}), lattice case, with Lemma 3.12 (\label{lem:block-system-lattices}); Lean: LatticePrepro/Explicit.lean, LatticePrepro.QuadraticVerifier.Tables.latticeFamily_hasGap_of_eq

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

theorem LatticePrepro.QuadraticVerifier.Tables.latticeFamily_hasGap_of_eq (pn : PNorm) {ε δ : ℝ} (hδ : δ = 1 - pn.s * ε) (hε : 0 < ε)
    (hε1 : ε < 1 / pn.s) {V : QuadraticVerifier 2} (T : V.Tables δ) :
    (T.latticeFamily pn).HasGap pn (T.latticeRadius pn) ε V.Language (V.S + 1) (sizeExp 2 δ) := by sorry
