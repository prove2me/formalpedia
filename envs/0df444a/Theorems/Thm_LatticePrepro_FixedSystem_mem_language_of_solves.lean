-- Prove2me | Theorems.Thm_LatticePrepro_FixedSystem_mem_language_of_solves
-- name    : LatticePrepro.FixedSystem.mem_language_of_solves
-- status  : Proved
-- author  : @WizardOfMenlo
-- created : 2026-11-13T09:25:30.800209+00:00
-- url     : https://prove2.me/theorems/149226fd-9c72-4d90-82c6-6ac5ac5de98d
-- title:
--   Theorem 4.6 (soundness, weight form) — a solution below the weight threshold certifies membership
-- statement:
--   Let $p$ be a prime, $K$ a field that is an $\mathbb{F}_p$-algebra, and $\Omega$ an extension field of $K$. Elements of $\mathbb{F}_p$ and $K$ are viewed in $\Omega$ through the algebra maps. Consider the fixed-verifier system $Av=b_x$ of Construction 4.5 for a quadratic verifier $V$ with language $L(V)\subseteq\{0,1\}^n$, a moment representation $R$ over $K$ (moment parameter $r$, $D$ blocks per evaluation table, coefficient functions on $\Omega$), and an encoding tuple. Let $x\in\{0,1\}^n$ and let $v\in\mathbb{F}_p^{\mathrm{Col}}$ satisfy all equations of the system for $x$. If
--   $$2\,\operatorname{wt}(v)<r\cdot D,$$
--   then $x\in L(V)$. Here $\operatorname{wt}$ is the Hamming weight.
--
--   This is the core of the soundness part of Theorem 4.6. The paper's proof assumes a solution of weight below $rD/2$ (in its notation $\kappa D_{\mathrm{tab}}/2$) and exhibits an accepting computation on $x$. Theorem 4.6 follows: if $2gN<r$ for the number $N$ of tables, then every solution of weight at most $g\cdot N\cdot D$ is below the threshold.
--
--   **Formalization Note** "$v$ satisfies the equations" is the predicate `Solves V R ε x v`, which is equivalent to $Av=b_x$ for the linear map of `fixedSystem`. $D$ is `R.numBlocks`, the number of blocks of a single table, not of the whole system.
-- source:
--   G. Weissenberg, G. Fenzi, Nearly Optimal Hardness for CVP and NCP with Preprocessing (STOC 2027 submission #847), Theorem 4.6 (\label{thm:fixed-verifier-reduction}), soundness part (weight form); Lean: LatticePrepro/Reduction/Soundness.lean, LatticePrepro.FixedSystem.mem_language_of_solves

import Mathlib
import Definitions.Def_LatticePrepro_Basic_Blocks
import Definitions.Def_LatticePrepro_Reduction_LinearSystem
import Definitions.Def_LatticePrepro_Moments_Basic
import Definitions.Def_LatticePrepro_Moments_Representation
import Definitions.Def_LatticePrepro_Verifier_Quadratic
import Definitions.Def_LatticePrepro_Reduction_FixedSystem

open LatticePrepro
open Finsupp
open LatticePrepro.FixedSystem
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K]
    {Ω : Type} [Field Ω] [Algebra (ZMod p) Ω] [Algebra K Ω] [IsScalarTower (ZMod p) K Ω]
    (V : QuadraticVerifier p) (R : MomentRepresentation p K Ω) (ε : EncodingTuple p K V.S)

theorem LatticePrepro.FixedSystem.mem_language_of_solves {x : Fin V.n → Bool} {v : Col V R → ZMod p}
    (hv : Solves V R ε x v) (hw : 2 * hammingNorm v < R.r * R.numBlocks) : x ∈ V.Language := by sorry
