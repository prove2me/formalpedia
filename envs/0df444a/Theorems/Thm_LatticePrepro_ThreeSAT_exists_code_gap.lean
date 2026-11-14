-- Prove2me | Theorems.Thm_LatticePrepro_ThreeSAT_exists_code_gap
-- name    : LatticePrepro.ThreeSAT.exists_code_gap
-- status  : Proved
-- author  : @WizardOfMenlo
-- created : 2026-11-13T15:49:13.558438+00:00
-- url     : https://prove2.me/theorems/66ca649e-ed82-4fee-9f04-fadd5484c664
-- title:
--   Theorem 5.1 (codes, 3SAT) — fixed codes with gap $M^{1-\varepsilon}$ for 3SAT
-- statement:
--   Let $p$ be a prime, let $F$ be a finite field of characteristic $p$ (a finite field that is an $\mathbb{F}_p$-algebra), and let $0 < \varepsilon < 1$. Then there is a constant $C \in \mathbb{N}$ such that for every number of variables $v \ge 1$, with $n = (2v)^3$ the instance length of 3SAT on $v$ variables, there exist
--
--   - a finite coordinate set of size $M$ with $1 \le M \le n^C$, a linear code $\mathcal C \subseteq F^M$, and a target $t_x \in F^M$ for every 3SAT instance $x$ on $v$ variables (the code depends only on $v$, the target on $x$);
--   - an integer radius $R \ge 1$,
--
--   such that, writing $d_H$ for Hamming distance and $d(t, \mathcal C) = \min_{c \in \mathcal C} d_H(t, c)$:
--
--   1. **YES instances.** If $x$ is satisfiable, then $d(t_x, \mathcal C) \le R$.
--   2. **NO instances.** If $x$ is unsatisfiable, then
--   $$d(t_x, \mathcal C) > M^{1-\varepsilon} \cdot R.$$
--
--   This is the code half of Theorem 5.1, instantiated with a verifier for 3SAT: one fixed code per number of variables separates satisfiable from unsatisfiable formulas with gap $M^{1-\varepsilon}$. It is the combinatorial core of the NCP part of Theorem 1.1; the remaining ingredients there (polynomial-time computability of code, radius and targets, and the complexity-theoretic argument) are not formalized.
--
--   **Formalization Note**: The conclusion is `Nonempty (CodeGap F ε (SAT v) (len v) C)`, a structure whose fields are the code family (`CodeFamily`: a finite coordinate type, a subspace `Submodule F (M → F)` and the targets), the radius, and the properties above. Instances are 3SAT formulas encoded by one bit per possible clause, so $n$ is `len v` $= (2v)^3$, and the families are indexed by $v \ge 1$ rather than by $n$; $C$ may depend on $p$, $F$ and $\varepsilon$ but not on $v$. The distance $d(t, \mathcal C)$ is the natural number `codeDist` (an `sInf` of Hamming distances), $M$ is `Fintype.card 𝒞.M`, and $M^{1-\varepsilon}$ is a real power. Polynomial-time computability, the generator-matrix presentation and the description-length bounds of Theorem 5.1 are not part of the statement, and neither is the search test of Lemma 5.2, which is stated separately for the concrete test.
-- source:
--   G. Weissenberg, G. Fenzi, Nearly Optimal Hardness for CVP and NCP with Preprocessing (STOC 2027 submission #847), Theorem 5.1 (\label{thm:approximation-hardness}), codes, for the 3SAT verifier; Lean: LatticePrepro/ThreeSAT.lean, LatticePrepro.ThreeSAT.exists_code_gap

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

theorem LatticePrepro.ThreeSAT.exists_code_gap (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Fintype F]
    [DecidableEq F] [Algebra (ZMod p) F] (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ C : ℕ, ∀ v : ℕ, 1 ≤ v → Nonempty (CodeGap F ε (SAT v) (len v) C) := by sorry
