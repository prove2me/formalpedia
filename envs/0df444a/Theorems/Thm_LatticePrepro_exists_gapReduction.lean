-- Prove2me | Theorems.Thm_LatticePrepro_exists_gapReduction
-- name    : LatticePrepro.exists_gapReduction
-- status  : Proved
-- author  : @WizardOfMenlo
-- created : 2026-11-13T15:49:06.244847+00:00
-- url     : https://prove2.me/theorems/62067329-2d81-4172-a3b7-66355436ffda
-- title:
--   Theorem 4.8 — size and gap of the fixed linear system
-- statement:
--   Let $p$ be a prime, let $V$ be a quadratic verifier over $\mathbb{F}_p$ with instance length $n$, $S$ assignment coordinates and language $L(V)\subseteq\{0,1\}^n$, and let $g\ge1$ and $m\ge1$ be integers. Then there is a linear system family over $\mathbb{F}_p$, consisting of a fixed $\mathbb{F}_p$-linear map $A$ on $\mathbb{F}_p^{N_{\mathrm{col}}}$, a right-hand side $b_x$ for every $x\in\{0,1\}^n$, and a partition of the $N_{\mathrm{col}}$ columns into $D$ blocks of size $b$, with the following properties.
--
--   1. **Completeness.** For every $x\in L(V)$, the system $Av=b_x$ has a solution $v\in\{0,1\}^{N_{\mathrm{col}}}$ with at most one nonzero coordinate in each block.
--   2. **Soundness.** For every $x\notin L(V)$, every solution $v\in\mathbb{F}_p^{N_{\mathrm{col}}}$ of $Av=b_x$ has Hamming weight $\operatorname{wt}(v)>g\cdot D$.
--   3. **Block structure.** $g<b$, the block size is a power of $p$ ($b=p^e$ for some $e\ge0$), and $D\ge1$.
--   4. **Size.** The number of columns satisfies
--   $$N_{\mathrm{col}}^{\,m}\le\bigl(8\,p^4\,m\,(S+1)\bigr)^{(m+7)m}\cdot g^{m+1}.$$
--
--   This is Theorem 4.8 of the paper without its running-time claims. Items 1 and 2 say that $x\mapsto b_x$ reduces $L(V)$ to $(D,b,g)$-BSLSP (Definition 3.10). Item 4 is the bound (22), $N_{\mathrm{col}}\le(8p^4m(S+1))^{m+7}g^{1+1/m}$, raised to the $m$-th power. In the paper's notation, $S,g,m,b,N_{\mathrm{col}}$ are $N,\Gamma,\mathsf{a},Q,n_{\mathrm{sys}}$. The theorem feeds the code and lattice conversions in the proof of Theorem 5.1 (`code_gap`, `lattice_gap`).
--
--   **Formalization Note** The conclusion is `Nonempty (GapReduction p V g m)`, a structure bundling the system with the properties above. The verifier is an abstract `QuadraticVerifier`: a system of quadratic gate equations over $\mathbb{F}_p$ with a designated input prefix and output coordinate. Claim 3.15 produces one from a Boolean circuit. The size bound is kept in integer form. The paper's statement also includes the time bounds and the uniform size bound (24) for a choice of $m$ depending on $S$ and $g$; these are not part of the Lean statement. The facts that $b$ is a power of $p$ and $D\ge1$ are extra conclusions that the paper's statement does not list explicitly.
-- source:
--   G. Weissenberg, G. Fenzi, Nearly Optimal Hardness for CVP and NCP with Preprocessing (STOC 2027 submission #847), Theorem 4.8 (\label{thm:quantitative-affine-gap}); Lean: LatticePrepro/Main.lean, LatticePrepro.exists_gapReduction

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

theorem LatticePrepro.exists_gapReduction (p : ℕ) [hp : Fact p.Prime] (V : QuadraticVerifier p) (g m : ℕ)
    (hg : 1 ≤ g) (hm : 1 ≤ m) : Nonempty (GapReduction p V g m) := by sorry
