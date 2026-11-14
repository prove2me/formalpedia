-- Prove2me | Theorems.Thm_LatticePrepro_FixedSystem_isGapReduction
-- name    : LatticePrepro.FixedSystem.isGapReduction
-- status  : Proved
-- author  : @WizardOfMenlo
-- created : 2026-11-13T09:25:24.190097+00:00
-- url     : https://prove2.me/theorems/ac746b71-16ac-42a8-8609-982f8be48b2b
-- title:
--   Theorem 4.6 — the fixed-verifier system is a gap reduction to block-sparse linear systems
-- statement:
--   Let $p$ be a prime, $K$ a field that is an $\mathbb{F}_p$-algebra, and $\Omega$ an extension field of $K$. Elements of $\mathbb{F}_p$ and $K$ are viewed in $\Omega$ through the algebra maps. Let:
--   - $V$ be a quadratic verifier over $\mathbb{F}_p$ with instance length $n$, $S$ assignment coordinates and language $L(V)\subseteq\{0,1\}^n$;
--   - $R$ be a moment representation over $K$, with moment parameter $r$, $D$ blocks per evaluation table and block size $b$, whose soundness produces coefficient functions on $\Omega$;
--   - $E_0=0,E_1,\dots,E_S\in K$ be an encoding tuple ($E_1,\dots,E_S$ linearly independent over $\mathbb{F}_p$).
--
--   Let $Av=b_x$ be the fixed-verifier system of Construction 4.5. It has $N$ evaluation tables, $N\cdot D$ blocks of size $b$, and the matrix $A$ does not depend on $x$. Let $g\in\mathbb{N}$ satisfy
--   $$2\,g\,N<r.$$
--   Then:
--   1. **Completeness.** For every $x\in L(V)$ there is a binary vector $v$ with $Av=b_x$ and at most one nonzero coordinate in each block.
--   2. **Soundness.** For every $x\notin L(V)$, every $v$ over $\mathbb{F}_p$ with $Av=b_x$ has Hamming weight $\operatorname{wt}(v)>g\cdot N\cdot D$.
--
--   So $x\mapsto b_x$ reduces $L(V)$ to the block-sparse linear-system problem with gap $g$ (Definition 3.10).
--
--   This is Theorem 4.6 of the paper; in its notation, $N,g,r,D$ are $\sigma,\Gamma,\kappa,D_{\mathrm{tab}}$. Theorem 4.8 applies it with the explicit moment representation of Appendix A.
--
--   **Formalization Note** The conclusion is `(fixedSystem V R ε).IsGapReduction V.Language g`, where `ε` is the encoding tuple and $N$ is `Fintype.card V.TblIdx`. The paper also assumes $g\ge1$ and $g<b$, which make the target a $(N\cdot D,b,g)$-BSLSP instance in the sense of Definition 3.10; the Lean statement does not need them. $K$ is not required to be finite. The time bound of the paper is not formalized. The verifier is given by quadratic gate equations rather than a Boolean circuit (compare Claim 3.15).
-- source:
--   G. Weissenberg, G. Fenzi, Nearly Optimal Hardness for CVP and NCP with Preprocessing (STOC 2027 submission #847), Theorem 4.6 (\label{thm:fixed-verifier-reduction}); Lean: LatticePrepro/Reduction/Soundness.lean, LatticePrepro.FixedSystem.isGapReduction

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

theorem LatticePrepro.FixedSystem.isGapReduction {g : ℕ} (hg : 2 * g * Fintype.card V.TblIdx < R.r) :
    (fixedSystem V R ε).IsGapReduction V.Language g := by sorry
