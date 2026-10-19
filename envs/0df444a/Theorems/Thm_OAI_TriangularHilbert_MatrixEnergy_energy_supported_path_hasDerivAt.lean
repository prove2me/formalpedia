-- Prove2me | Theorems.Thm_OAI_TriangularHilbert_MatrixEnergy_energy_supported_path_hasDerivAt
-- name    : OAI.TriangularHilbert.MatrixEnergy.energy_supported_path_hasDerivAt
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T01:42:45.016902+00:00
-- url     : https://prove2.me/theorems/b22ba586-f542-42d3-8a11-47128dd02faa
-- title:
--   Differentiating the energy along a path with fixed kernel
-- statement:
--   For complex square matrices, $\operatorname{tr}_{\mathbb R}(A)=\operatorname{Re}\operatorname{tr}A$ and $\langle X,Y\rangle=\operatorname{Re}\operatorname{tr}(X^*Y)$. The matrix energy of $P\ge0$ is $E(P)=\operatorname{Re}\operatorname{tr}(P\sqrt P)=\operatorname{tr}P^{3/2}$, and $\mathrm{sylv}_A(X)=AX+XA$. Let $t\mapsto P(t)$ be differentiable at $x$ with derivative $U$. Suppose that near $x$ each $P(t)$ is positive semidefinite with $P(t)Q=0$ for a fixed orthogonal projection $Q$, and $P(x)+Q$ is positive definite. Then
--   $$
--   \frac{d}{dt}\Big|_{t=x}E(P(t))=\frac32\operatorname{Re}\operatorname{tr}\bigl(\sqrt{P(x)}\,U\bigr).
--   $$
--
--   The energy is differentiable along paths whose kernel contains a fixed complement.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/TriangularHilbert/Support.lean#L190-L207

import Mathlib
import Definitions.Def_TriangularHilbert
import Definitions.Def_OAI_Analysis_TriangularHilbert_Gaussian
import Definitions.Def_OAI_Analysis_TriangularHilbert_MeshMass
import Definitions.Def_OAI_Analysis_TriangularHilbert_GaussianMoments
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedWindowScalar
import Definitions.Def_OAI_Analysis_TriangularHilbert_MatrixSupport
import Definitions.Def_OAI_Analysis_TriangularHilbert_Support

open OAI OAI.TriangularHilbert OAI.TriangularHilbert.MatrixEnergy
universe uι
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators Topology
open Filter Unitary
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

theorem OAI.TriangularHilbert.MatrixEnergy.energy_supported_path_hasDerivAt {P : ℝ → Matrix ι ι ℂ}
    {Q U : Matrix ι ι ℂ} {x : ℝ}
    (hQ : Q.PosSemidef) (hQQ : Q * Q = Q) (hPD : (P x + Q).PosDef)
    (hn : ∀ᶠ t in 𝓝 x, (P t).PosSemidef) (hz : ∀ᶠ t in 𝓝 x, P t * Q = 0)
    (hd : HasDerivAt P U x) :
    HasDerivAt (fun t => energy (P t)) (energyGradient (P x) U) x := by sorry
