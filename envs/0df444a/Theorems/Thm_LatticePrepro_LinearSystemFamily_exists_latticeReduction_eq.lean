-- Prove2me | Theorems.Thm_LatticePrepro_LinearSystemFamily_exists_latticeReduction_eq
-- name    : LatticePrepro.LinearSystemFamily.exists_latticeReduction_eq
-- status  : Proved
-- author  : @WizardOfMenlo
-- created : 2026-11-20T00:15:42.379232+00:00
-- url     : https://prove2.me/theorems/6c8bf2e8-d82c-4dfd-a3c3-f8754c5ea44c
-- title:
--   Lemma 3.12 for the paper's lattice — the reduction is realized by Construction A and its Walsh–Hadamard transform
-- statement:
--   Let $L$ be a linear-system family over $\mathbb F_p$ with $D\ge1$ blocks of size $b$, let $g<b$ be an integer, and let $p'\ge1$ be a real norm exponent or $p'=\infty$, with $s=\min\{p',2\}$. Let $\Lambda$ be the lattice of the paper for $L$ and $p'$: the Construction A lattice of the padded code if $p'\le2$, and its blockwise Walsh–Hadamard transform otherwise, with its integer targets $t_x$. Let $R$ be the radius $\lceil D^{1/p'}\rceil$ for $p'\le2$, $\lceil(2^{k}D)^{1/p'}\rceil$ for $2<p'<\infty$, and $1$ for $p'=\infty$, where $2^{k}$ is the padded block size.
--
--   Then $\Lambda$ and $R$ are the lattice and the radius of a lattice reduction in the sense of Lemma 3.12. That is, with $n$ the number of columns of $L$ and $M$ the dimension of $\Lambda$:
--
--   - $2n\le M<4n$, $1\le R\le M$, and $N\cdot\mathbb Z^{M}\subseteq\Lambda$ for some integer $N>0$;
--   - for every YES instance $x$ there is $v\in\Lambda$ with $\|t_x-v\|_{p'}\le R$;
--   - there is a residual weight $w(x,v)\in\mathbb N$ with $w(x,v)\le16\cdot D\cdot(\|t_x-v\|_{p'}/R)^{s}$ for all $x$ and all $v\in\Lambda$, and $w(x,v)>g\cdot D$ for every NO instance $x$ and all $v\in\Lambda$.
--
--   This is Lemma 3.12 with the lattice named. The existence form (`exists_latticeReduction`) asserts that some lattice reduction exists; this statement says which lattice and radius it uses.
--
--   **Formalization Note.** The conclusion is the existence of a `LatticeReduction` whose lattice family equals `L.latticeFamily` and whose radius equals `L.latticeRadius`. The statement holds for every real $p'\ge1$ (the paper takes $p'$ rational). Computability of the lattice basis, of the targets and of the residual weight is not formalized.
-- source:
--   G. Fenzi, G. Weissenberg, Nearly Optimal Hardness for CVP and NCP with Preprocessing (STOC 2027 submission #847; IACR ePrint 2026/2634, https://eprint.iacr.org/2026/2634), Lemma 3.12 (\label{lem:block-system-lattices}) and its proof in Appendix B.3 (\label{subsec:gap-search-proof}); Lean: LatticePrepro/Explicit.lean, LatticePrepro.LinearSystemFamily.exists_latticeReduction_eq

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
open LatticePrepro.LinearSystemFamily
variable {p : ℕ} [Fact p.Prime] {X : Type} (L : LinearSystemFamily (ZMod p) X)

theorem LatticePrepro.LinearSystemFamily.exists_latticeReduction_eq {g : ℕ} (hg : g < L.blockSize) (hD : 0 < L.numBlocks)
    (pn : PNorm) :
    ∃ Red : LatticeReduction L g pn, Red.Λ = L.latticeFamily pn ∧ Red.R = L.latticeRadius pn := by sorry
