-- Prove2me | Theorems.Thm_OAI_BeamLadder_numberL_minus
-- name    : OAI.BeamLadder.numberL_minus
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T01:34:45.070971+00:00
-- url     : https://prove2.me/theorems/16abbaeb-2253-4b49-af65-0d34b1294283
-- title:
--   Left-port weighted lowering followed by raising acts as the mode number times $W^{-2}$
-- statement:
--   Let $\mathcal J_n = \ell^2(\mathbb{N}^n \times \mathbb{N}^n)$ be the two-port Fock space, with coordinates indexed by pairs $(k,m)$ of photon-number vectors. Put $w(k) = 1 + k_1 + \dots + k_n$ and $W(k,m) = w(k) + w(m) - 1$, and for a mode $j$ let $\mathbf 1_j$ be the $j$-th unit index. Define the bounded operators
--   $$
--   (A_jX)(k,m) = \frac{\sqrt{k_j+1}}{W(k,m)+1}\,X(k+\mathbf 1_j, m), \qquad (VX)(k,m) = \frac{X(k,m)}{W(k,m)},
--   $$
--   the left raising operator $R_j = \iota(W)\,A_j^{*}$, where $\iota(W)$ multiplies the $(k,m)$ coordinate by $W/(W-1)$ if $W(k,m) > 1$ and by $0$ otherwise, and the pre-lowering operator $P_j = A_j(I - V)$. Formally $A_j = a_j W^{-1}$ and $R_j = a_j^\dagger W^{-1}$ with $a_j, a_j^\dagger$ acting on the first port.
--
--   **Theorem.** For every $X \in \mathcal J_n$, every mode $j$ and all $k, m \in \mathbb{N}^n$,
--   $$
--   \big(R_j P_j X\big)(k,m) = k_j\,W(k,m)^{-2}\,X(k,m) = k_j\,(V^2X)(k,m) .
--   $$
--
--   So $R_jP_j$ is the diagonal operator $N_j W^{-2}$, where $N_j$ is the number operator of mode $j$ of the first port. This identity converts the "lowering then raising" terms of the two-port generator into number-weighted terms, which is how the anticommutator part of the dissipator appears in the beam-splitter computations.
--
--   **Formalization Note** $A_j$ is `BeamLadder.lowerL j`, $V$ is `BeamLadder.inverse`, $R_j$ is `raiseL j = radial increase … ∘L (lowerL j).adjoint`, $P_j$ is `preLowerL j = lowerL j ∘L (1 - inverse)`, and $W$ is `BeamLadder.W`. The right-hand side is written `(k j : ℂ) * inverse (inverse x) (k,e)`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/PhotonNumber/BeamForms.lean#L454-L468

import Mathlib
import Definitions.Def_EntropyPhotonNumber
import Definitions.Def_OAI_MathematicalPhysics_Fock_Beam
import Definitions.Def_OAI_Analysis_QuantumTrace_Basic
import Definitions.Def_OAI_MathematicalPhysics_Fock_Operators
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Gibbs
import Definitions.Def_OAI_Analysis_TensorLp
import Definitions.Def_OAI_InformationTheory_PhotonNumber_BeamTrace
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Functions
import Definitions.Def_OAI_Analysis_DiagonalForms
import Definitions.Def_OAI_InformationTheory_PhotonNumber_ThermalMetric
import Definitions.Def_OAI_InformationTheory_PhotonNumber_BeamForms

open OAI OAI.BeamLadder
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open ContinuousLinearMap
open scoped ENNReal
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
open scoped ComplexConjugate
variable {n : ℕ}

theorem OAI.BeamLadder.numberL_minus (j : Fin n) (x : JointFock n) (k e : NumberIndex n) :
    raiseL j (preLowerL j x) (k,e)=(k j:ℂ)*inverse (inverse x) (k,e) := by sorry
