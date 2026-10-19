-- Prove2me | Theorems.Thm_OAI_TriangularHilbert_MatrixEnergy_energyGradient_supported_path_hasDerivAt
-- name    : OAI.TriangularHilbert.MatrixEnergy.energyGradient_supported_path_hasDerivAt
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T01:43:22.375719+00:00
-- url     : https://prove2.me/theorems/96fe9e31-49c6-47bf-8747-b48d1b2232e9
-- title:
--   Second-order derivative of the energy along supported paths
-- statement:
--   For complex square matrices, $\operatorname{tr}_{\mathbb R}(A)=\operatorname{Re}\operatorname{tr}A$ and $\langle X,Y\rangle=\operatorname{Re}\operatorname{tr}(X^*Y)$. The matrix energy of $P\ge0$ is $E(P)=\operatorname{Re}\operatorname{tr}(P\sqrt P)=\operatorname{tr}P^{3/2}$, and $\mathrm{sylv}_A(X)=AX+XA$. Let $P(t)$ and $K(t)$ be differentiable at $x$ with derivatives $U$ and $V$. Suppose that near $x$, $P(t)\ge0$, $P(t)Q=0$, $K(t)$ is Hermitian and $K(t)Q=0$ for a fixed orthogonal projection $Q$, and $P(x)+Q$ is positive definite. Then
--   $$
--   \frac{d}{dt}\Big|_{t=x}\nabla E(P(t))[K(t)]=\mathrm{hessianPair}\bigl(P(x);K(x),U\bigr)+\nabla E(P(x))[V].
--   $$
--
--   This is the product rule for the gradient of the energy, with the Hessian pairing as the derivative of $\sqrt P$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/TriangularHilbert/Support.lean#L209-L235

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

theorem OAI.TriangularHilbert.MatrixEnergy.energyGradient_supported_path_hasDerivAt {P K : ℝ → Matrix ι ι ℂ}
    {Q U V : Matrix ι ι ℂ} {x : ℝ}
    (hQ : Q.PosSemidef) (hQQ : Q * Q = Q) (hPD : (P x + Q).PosDef)
    (hn : ∀ᶠ t in 𝓝 x, (P t).PosSemidef) (hz : ∀ᶠ t in 𝓝 x, P t * Q = 0)
    (hK : ∀ᶠ t in 𝓝 x, (K t).IsHermitian) (hkz : ∀ᶠ t in 𝓝 x, K t * Q = 0)
    (hdP : HasDerivAt P U x) (hdK : HasDerivAt K V x) :
    HasDerivAt (fun t => energyGradient (P t) (K t))
      (hessianPair (P x) (K x) U + energyGradient (P x) V) x := by sorry
