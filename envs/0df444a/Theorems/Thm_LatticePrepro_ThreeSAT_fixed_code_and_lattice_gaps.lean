-- Prove2me | Theorems.Thm_LatticePrepro_ThreeSAT_fixed_code_and_lattice_gaps
-- name    : LatticePrepro.ThreeSAT.fixed_code_and_lattice_gaps
-- status  : Proved
-- author  : @WizardOfMenlo
-- created : 2026-11-13T15:48:34.064064+00:00
-- url     : https://prove2.me/theorems/15ec6322-05cb-435b-963f-156a9b8edcd3
-- title:
--   Theorem 5.1 (fixed code and lattice gaps) for 3SAT — both parts
-- statement:
--   For 3SAT on $v$ variables, with instance length $n = (2v)^3$ (one bit per possible clause), both of the following hold.
--
--   1. **Codes.** For every prime $p$, every finite field $F$ of characteristic $p$, and every $0 < \varepsilon < 1$, there is $C \in \mathbb{N}$ such that for every $v \ge 1$ there are a linear code $\mathcal C \subseteq F^M$ with $1 \le M \le n^C$, targets $t_x \in F^M$ and an integer radius $R \ge 1$ with
--   $$x \text{ satisfiable} \Rightarrow d(t_x, \mathcal C) \le R, \qquad x \text{ unsatisfiable} \Rightarrow d(t_x, \mathcal C) > M^{1-\varepsilon}\cdot R,$$
--   where $d$ is the Hamming distance to the code.
--   2. **Lattices.** For every $1 \le p \le \infty$, with $s = \min\{p,2\}$, and every $0 < \varepsilon < 1/s$, there is $C \in \mathbb{N}$ such that for every $v \ge 1$ there are a full-rank lattice $\Lambda \subseteq \mathbb{Z}^M$ (containing $N\cdot\mathbb{Z}^M$ for some integer $N > 0$) with $1 \le M \le n^C$, integer targets $t_x$ and an integer radius $R \ge 1$ with
--   $$x \text{ satisfiable} \Rightarrow \operatorname{dist}_p(t_x, \Lambda) \le R, \qquad x \text{ unsatisfiable} \Rightarrow \operatorname{dist}_p(t_x, \Lambda) > M^{1/s-\varepsilon}\cdot R,$$
--   where $\operatorname{dist}_p(t,\Lambda) = \inf_{u\in\Lambda}\|t-u\|_p$.
--
--   This is the paper's Theorem 5.1 for the 3SAT verifier, and the final theorem of the formalization; it is the conjunction of `ThreeSAT.exists_code_gap` and `ThreeSAT.exists_lattice_gap`.
--
--   **Formalization Note**: The two parts assert `Nonempty (CodeGap F ε (SAT v) (len v) C)` and `Nonempty (LatticeGap pn ε (SAT v) (len v) C)`; the constant $C$ is chosen before $v$, so it depends only on the field (resp. norm exponent) and $\varepsilon$. Code distances are natural numbers (`codeDist`), lattice distances are real infima (`latticeDist`), $p$ ranges over all reals $p \ge 1$ and $\infty$ (`PNorm`), and $M^{\cdot}$ is a real power. Polynomial-time computability and description lengths are not formalized. The search test of Lemma 5.2 is a separate milestone for the paper's concrete tests; it is not bundled here, since without its running-time bound an abstract test would be satisfied by satisfiability itself.
-- source:
--   G. Weissenberg, G. Fenzi, Nearly Optimal Hardness for CVP and NCP with Preprocessing (STOC 2027 submission #847), Theorem 5.1 (\label{thm:approximation-hardness}) for the 3SAT verifier; Lean: LatticePrepro/ThreeSAT.lean, LatticePrepro.ThreeSAT.fixed_code_and_lattice_gaps

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

theorem LatticePrepro.ThreeSAT.fixed_code_and_lattice_gaps :
    (∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Fintype F] [DecidableEq F]
        [Algebra (ZMod p) F] (ε : ℝ), 0 < ε → ε < 1 →
        ∃ C : ℕ, ∀ v : ℕ, 1 ≤ v → Nonempty (CodeGap F ε (SAT v) (len v) C)) ∧
      (∀ (pn : PNorm) (ε : ℝ), 0 < ε → ε < 1 / pn.s →
        ∃ C : ℕ, ∀ v : ℕ, 1 ≤ v → Nonempty (LatticeGap pn ε (SAT v) (len v) C)) := by sorry
