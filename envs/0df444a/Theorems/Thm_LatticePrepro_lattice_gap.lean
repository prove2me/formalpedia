-- Prove2me | Theorems.Thm_LatticePrepro_lattice_gap
-- name    : LatticePrepro.lattice_gap
-- status  : Proved
-- author  : @WizardOfMenlo
-- created : 2026-11-13T15:48:32.300696+00:00
-- url     : https://prove2.me/theorems/98440f85-aa39-4736-a6d5-6172a67b4e50
-- title:
--   Theorem 5.1 (lattices) — fixed lattice with gap $M^{1/s-\varepsilon}$ in $\ell_p$ for any quadratic verifier over $\mathbb{F}_2$, explicit exponent
-- statement:
--   Let $1\le p\le\infty$ be a norm exponent (any real $p\ge1$, or $p=\infty$), and let $s=\min\{p,2\}$, with $s=2$ for $p=\infty$. Let $0<\varepsilon<1/s$. Let $V$ be a quadratic verifier over $\mathbb{F}_2$ with instance length $n$, $S$ assignment coordinates and language $L(V)\subseteq\{0,1\}^n$, and let
--   $$C=\mathrm{sizeExp}(2,\,1-s\varepsilon),$$
--   an explicit exponent depending only on $s\varepsilon$. Then there are a dimension $M$, a lattice $\Lambda\subseteq\mathbb{Z}^M$ (a $\mathbb{Z}$-submodule), an integer target $t_x\in\mathbb{Z}^M$ for every $x\in\{0,1\}^n$, an integer radius $R\ge1$ and an integer $N\ge1$ such that:
--
--   1. $1\le M\le(S+1)^C$;
--   2. $N\cdot\mathbb{Z}^M\subseteq\Lambda$, so $\Lambda$ has full rank;
--   3. for every $x\in L(V)$, $\operatorname{dist}_p(t_x,\Lambda)\le R$;
--   4. for every $x\notin L(V)$, $\operatorname{dist}_p(t_x,\Lambda)>M^{1/s-\varepsilon}\cdot R$.
--
--   Here $\|\cdot\|_p$ is the $\ell_p$ norm on $\mathbb{R}^M$ (the maximum norm for $p=\infty$) and $\operatorname{dist}_p(t,\Lambda)=\inf_{v\in\Lambda}\|t-v\|_p$. In short,
--   $$x\in L(V)\Rightarrow\operatorname{dist}_p(t_x,\Lambda)\le R,\qquad x\notin L(V)\Rightarrow\operatorname{dist}_p(t_x,\Lambda)>M^{1/s-\varepsilon}\cdot R.$$
--   The lattice $\Lambda$ and the radius $R$ do not depend on $x$; only the target $t_x$ does.
--
--   This is the lattice case of Theorem 5.1. As in the paper's proof, the verifier is over $\mathbb{F}_2$. The result is stated for an arbitrary quadratic verifier, with dimension bounded by $(S+1)^C$. The paper fixes a 3SAT verifier and obtains $M=\mathrm{poly}(n)$; that instantiation is a separate Lean result. The paper allows rational $p$; here every real $p\ge1$ is allowed.
--
--   **Formalization Note** The conclusion is `Nonempty (LatticeGap pn ε V.Language (V.S + 1) C)`, where `pn : PNorm` encodes $p$. The lattice distance is a real infimum (`⨅` over lattice vectors), and $M^{1/s-\varepsilon}$ is a real power (`Real.rpow`). Polynomial-time computability and description lengths are not formalized; the search test of Lemma 5.2 is stated separately (`LatticeReduction.accepts_of_isApprox`, `LatticeReduction.not_accepts_of_isNo`).
-- source:
--   G. Weissenberg, G. Fenzi, Nearly Optimal Hardness for CVP and NCP with Preprocessing (STOC 2027 submission #847), Theorem 5.1 (\label{thm:approximation-hardness}), lattice case; Lean: LatticePrepro/Main.lean, LatticePrepro.lattice_gap

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

theorem LatticePrepro.lattice_gap (pn : PNorm) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1 / pn.s)
    (V : QuadraticVerifier 2) :
    Nonempty (LatticeGap pn ε V.Language (V.S + 1) (sizeExp 2 (1 - pn.s * ε))) := by sorry
