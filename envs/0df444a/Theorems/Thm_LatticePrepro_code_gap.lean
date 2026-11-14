-- Prove2me | Theorems.Thm_LatticePrepro_code_gap
-- name    : LatticePrepro.code_gap
-- status  : Proved
-- author  : @WizardOfMenlo
-- created : 2026-11-13T15:49:14.333428+00:00
-- url     : https://prove2.me/theorems/7e461637-c4ce-4f58-b8dc-b8866f0bca80
-- title:
--   Theorem 5.1 (codes) — fixed code with gap $M^{1-\varepsilon}$ for any quadratic verifier, explicit exponent
-- statement:
--   Let $p$ be a prime, $F$ a finite field of characteristic $p$, and $0<\varepsilon<1$. Let $V$ be a quadratic verifier over $\mathbb{F}_p$ with instance length $n$, $S$ assignment coordinates and language $L(V)\subseteq\{0,1\}^n$. Let
--   $$C=\mathrm{sizeExp}(p,1-\varepsilon),$$
--   the explicit exponent of the parameter choice, which depends only on $p$ and $\varepsilon$. Then there are a finite block length $M$, an $F$-linear code $\mathcal{C}\subseteq F^M$, a target $t_x\in F^M$ for every $x\in\{0,1\}^n$, and an integer radius $R\ge1$ such that:
--
--   1. $1\le M\le(S+1)^C$;
--   2. for every $x\in L(V)$, $\operatorname{dist}(t_x,\mathcal{C})\le R$;
--   3. for every $x\notin L(V)$, $\operatorname{dist}(t_x,\mathcal{C})>M^{1-\varepsilon}\cdot R$.
--
--   Here $d_H$ is the Hamming distance and $\operatorname{dist}(y,\mathcal{C})=\min_{c\in\mathcal{C}}d_H(y,c)$. In short,
--   $$x\in L(V)\Rightarrow\operatorname{dist}(t_x,\mathcal{C})\le R,\qquad x\notin L(V)\Rightarrow\operatorname{dist}(t_x,\mathcal{C})>M^{1-\varepsilon}\cdot R.$$
--   The code $\mathcal{C}$ and the radius $R$ do not depend on $x$; only the target $t_x$ does.
--
--   This is the code case ($s=1$) of Theorem 5.1. It is stated for an arbitrary quadratic verifier, with block length bounded by $(S+1)^C$. The paper instead fixes a 3SAT verifier and obtains $M=\mathrm{poly}(n)$; that instantiation is a separate Lean result.
--
--   **Formalization Note** The conclusion is `Nonempty (CodeGap F ε V.Language (V.S + 1) C)`. The characteristic of $F$ is expressed by an `Algebra (ZMod p) F` instance. The code distance is a natural number defined via `sInf`, and $M^{1-\varepsilon}$ is a real power (`Real.rpow`). Polynomial-time computability of the code and targets is not formalized; the search test of Lemma 5.2 is stated separately (`CodeFamily.accepts_of_isApprox`, `CodeFamily.not_accepts_of_lt`).
-- source:
--   G. Weissenberg, G. Fenzi, Nearly Optimal Hardness for CVP and NCP with Preprocessing (STOC 2027 submission #847), Theorem 5.1 (\label{thm:approximation-hardness}), code case; Lean: LatticePrepro/Main.lean, LatticePrepro.code_gap

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

open LatticePrepro

theorem LatticePrepro.code_gap (p : ℕ) [hp : Fact p.Prime] (F : Type) [Field F] [Fintype F]
    [DecidableEq F] [Algebra (ZMod p) F] (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (V : QuadraticVerifier p) :
    Nonempty (CodeGap F ε V.Language (V.S + 1) (sizeExp p (1 - ε))) := by sorry
