-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_jacquetVector3_iotaGL_diagUnitGL2_mul
-- name    : LanglandsTunnell.CubicInduction.jacquetVector3_iotaGL_diagUnitGL2_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/4a3497c4-f08e-5516-b66d-f51a0f6df881
-- title:
--   Torus dilation law for the GL₃ Jacquet vector
-- statement:
--   Fix an archimedean parameter $P$ of `RealArchParam` type (either `principal` with data $u_1,a_1,u_2,a_2$ or `discrete` with data $u,k$ and $1\le k$), and let $D$ be an `ArchDatumR P`, i.e. a package consisting of a function $W$ on the real $2\times 2$ matrices together with smoothness on the invertible locus, the unipotent law $W(\mathrm{unip}(x)g)=\psi_0(x)W(g)$, the central law governing $W(z\cdot g)$ by the central character of $P$ and $|z|$, an entire zeta function with its integral representation against $\operatorname{archFactor}$, functional equation, finite-order bounds, and decay estimates at large and small $y$. Let further $u_3\in\mathbb C$, $a_3\in\mathbb Z/2$, $a\in\mathbb R$, let $\psi$ be a $\mathbb C$-valued additive character of the infinite adele ring of $\mathbb Q$, let $S$ be a complex-valued function on the real $2\times 3$ matrices, let $z$ be a unit of the infinite adele ring of $\mathbb Q$ and $g\in\mathrm{GL}_3$ over that ring; no further hypotheses are imposed on $z$ or $g$. Here `jacquetVector3 D u₃ a₃ a ψ S g` is the product of `quasiChar (u₃ + 1) a₃` evaluated at the determinant of the real $3\times 3$ matrix attached to $g$ with the integral over $e\in\mathbb R^{2\times 2}$ of `jacquetIntegrand3 D u₃ a₃ a ψ S g e`. The assertion is that its value at the left translate of $g$ by the image under the block embedding `iotaGL` of the $2\times 2$ invertible matrix $\operatorname{diag}(z,1)$, that is at $\operatorname{diag}(z,1,1)\,g$, equals its value at $g$ with the real parameter $a$ replaced by $a\cdot\operatorname{realCoord}(z)$, where $\operatorname{realCoord}$ is the ring homomorphism from the infinite adele ring of $\mathbb Q$ to $\mathbb R$ given by evaluation at the infinite place followed by the identification of its completion with $\mathbb R$.
--
--   This is the torus, or dilation, law for the Jacquet vector built from a Whittaker datum on $\mathrm{GL}_2(\mathbb R)$ and a Schwartz-type section $S$: translating on the left by the torus element $\operatorname{diag}(z,1,1)$ is absorbed into a rescaling of the real parameter $a$. It is used in the computation of the archimedean zeta integrals attached to such vectors, for instance in the identification of those integrals with $\operatorname{archFactor}$ times an entire function and in the corresponding dual statement.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_jacquetVector3_iotaGL_diagUnitGL2_mul.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_IotaTorus
import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetVector3

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField AutomorphicForm LanglandsTunnell.Converse

theorem LanglandsTunnell.CubicInduction.jacquetVector3_iotaGL_diagUnitGL2_mul
    {P : RealArchParam} (D : ArchDatumR P) (u₃ : ℂ) (a₃ : ZMod 2) (a : ℝ)
    (ψ : AddChar (InfiniteAdeleRing ℚ) ℂ) (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ)
    (z : (InfiniteAdeleRing ℚ)ˣ) (g : GL (Fin 3) (InfiniteAdeleRing ℚ)) :
    jacquetVector3 D u₃ a₃ a ψ S (iotaGL (diagUnitGL2 z) * g) =
      jacquetVector3 D u₃ a₃ (a * StandardKernel.realCoord (z : InfiniteAdeleRing ℚ)) ψ S g := by sorry
