-- Prove2me | Theorems.Thm_LatticePrepro_ThreeSAT_exists_lattice_gap
-- name    : LatticePrepro.ThreeSAT.exists_lattice_gap
-- status  : Proved
-- author  : @WizardOfMenlo
-- created : 2026-11-13T15:49:59.74666+00:00
-- url     : https://prove2.me/theorems/5d752087-ea8f-41d9-885a-171f72015cc8
-- title:
--   Theorem 5.1 (lattices, 3SAT) — fixed lattices with gap $M^{1/s-\varepsilon}$ in every $\ell_p$ norm
-- statement:
--   Let $1 \le p \le \infty$ (a real number $p \ge 1$, or $p = \infty$), let $s = \min\{p, 2\}$ (so $s = 2$ for $p = \infty$), and let $0 < \varepsilon < 1/s$. Then there is a constant $C \in \mathbb{N}$ such that for every number of variables $v \ge 1$, with $n = (2v)^3$ the instance length of 3SAT on $v$ variables, there exist
--
--   - a finite coordinate set of size $M$ with $1 \le M \le n^C$, a lattice $\Lambda \subseteq \mathbb{Z}^M$ (a subgroup) containing $N \cdot \mathbb{Z}^M$ for some integer $N > 0$, so that $\Lambda$ has full rank, and an integer target $t_x \in \mathbb{Z}^M$ for every 3SAT instance $x$ on $v$ variables;
--   - an integer radius $R \ge 1$,
--
--   such that, writing $\|\cdot\|_p$ for the $\ell_p$ norm and $\operatorname{dist}_p(t, \Lambda) = \inf_{u \in \Lambda} \|t - u\|_p$:
--
--   1. **YES instances.** If $x$ is satisfiable, then $\operatorname{dist}_p(t_x, \Lambda) \le R$.
--   2. **NO instances.** If $x$ is unsatisfiable, then
--   $$\operatorname{dist}_p(t_x, \Lambda) > M^{1/s-\varepsilon} \cdot R.$$
--
--   This is the lattice half of Theorem 5.1, instantiated with a verifier for 3SAT: one fixed lattice per number of variables separates satisfiable from unsatisfiable formulas with gap $M^{1/s-\varepsilon}$. It is the combinatorial core of the CVP part of Theorem 1.1; the remaining ingredients there (polynomial-time computability and the complexity-theoretic argument) are not formalized.
--
--   **Formalization Note**: The conclusion is `Nonempty (LatticeGap pn ε (SAT v) (len v) C)`, a structure bundling the lattice family (`LatticeFamily`: a finite coordinate type, a `Submodule ℤ (M → ℤ)` and the targets), $R$, $N$ and the properties above. The norm exponent is a `PNorm`: any real $p \ge 1$ (the paper states rational $p$, which only matters for computability) or $p = \infty$; $\|v\|_p = (\sum_i |v_i|^p)^{1/p}$ uses real powers and $\|v\|_\infty = \max_i |v_i|$. $\operatorname{dist}_p$ is the real infimum `latticeDist`, and full rank is expressed by $N\cdot\mathbb{Z}^M \subseteq \Lambda$. Instances are encoded by one bit per possible clause ($n$ is `len v` $= (2v)^3$) and indexed by $v \ge 1$; $C$ may depend on $p$ and $\varepsilon$ but not on $v$. Polynomial-time computability, the description-length bounds and the search test of Lemma 5.2 (stated separately for the concrete test) are not part of the statement.
-- source:
--   G. Weissenberg, G. Fenzi, Nearly Optimal Hardness for CVP and NCP with Preprocessing (STOC 2027 submission #847), Theorem 5.1 (\label{thm:approximation-hardness}), lattices, for the 3SAT verifier; Lean: LatticePrepro/ThreeSAT.lean, LatticePrepro.ThreeSAT.exists_lattice_gap

import Mathlib
import Definitions.Def_LatticePrepro_Basic_Blocks
import Definitions.Def_LatticePrepro_Reduction_LinearSystem
import Definitions.Def_LatticePrepro_Conversions_Codes
import Definitions.Def_LatticePrepro_Conversions_ConstructionA
import Definitions.Def_LatticePrepro_Conversions_Hadamard
import Definitions.Def_LatticePrepro_Conversions_Lattices
import Definitions.Def_LatticePrepro_Lattices_Distance
import Definitions.Def_LatticePrepro_Lattices_Mathlib
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
import Definitions.Def_LatticePrepro_Main
import Definitions.Def_LatticePrepro_Verifier_Gates
import Definitions.Def_LatticePrepro_Verifier_Circuit
import Definitions.Def_LatticePrepro_Verifier_Expr
import Definitions.Def_LatticePrepro_Verifier_ThreeSAT
import Definitions.Def_LatticePrepro_ThreeSAT

open LatticePrepro
open LatticePrepro.ThreeSAT

theorem LatticePrepro.ThreeSAT.exists_lattice_gap (pn : PNorm) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1 / pn.s) :
    ∃ C : ℕ, ∀ v : ℕ, 1 ≤ v → Nonempty (LatticeGap pn ε (SAT v) (len v) C) := by sorry
