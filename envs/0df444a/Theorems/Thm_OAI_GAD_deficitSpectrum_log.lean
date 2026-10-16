-- Prove2me | Theorems.Thm_OAI_GAD_deficitSpectrum_log
-- name    : OAI.GAD.deficitSpectrum_log
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:20:11.349969+00:00
-- url     : https://prove2.me/theorems/1167c2b6-4fbf-4fc6-a1b1-1468965a4816
-- title:
--   Logarithmic resolvent identity for the five-point deficit spectrum
-- statement:
--   For real numbers $x,y,z\ge0$ let
--   $$\lambda_\pm=\frac{(x+y+z)\pm\sqrt{(x+y+z)^2-4yz}}{2}$$
--   be the two roots of $\lambda^2-(x+y+z)\lambda+yz=0$; they are real and nonnegative. Consider the five-point spectrum $(x,y,z,\lambda_+,\lambda_-)$ with signs $(+1,+1,+1,-1,-1)$, and for $t>0$ define
--   $$\delta(x,y,z;t)=\log\Bigl(1+\frac{x}{t}\Bigr)-\log\Bigl(1+\frac{tx}{(t+y)(t+z)}\Bigr).$$
--   Then for all $x,y,z\ge0$ and all $t>0$ (natural logarithms),
--
--   $$
--   \log\Bigl(1+\frac xt\Bigr)+\log\Bigl(1+\frac yt\Bigr)+\log\Bigl(1+\frac zt\Bigr)-\log\Bigl(1+\frac{\lambda_+}t\Bigr)-\log\Bigl(1+\frac{\lambda_-}t\Bigr)=\delta(x,y,z;t).
--   $$
--
--   The signed entropy of the same spectrum, $\Delta(x,y,z)=\eta(x)+\eta(y)+\eta(z)-\eta(\lambda_+)-\eta(\lambda_-)$ with $\eta(w)=-w\log w$, is the scalar entropy deficit studied in this development. The identity computes the corresponding signed logarithmic resolvent sum in closed form, which is exactly the input needed to compare weighted sums of deficits $\Delta$ through the entropy comparison principle.
--
--   **Formalization Note** The spectrum and the signs are the vectors `deficitSpectrum x y z = ![x, y, z, λ₊, λ₋]` and `deficitSigns = ![1, 1, 1, -1, -1]` indexed by `Fin 5`; $\lambda_\pm$ are `blockLambdaPlus` and `blockLambdaMinus` (defined with `Real.sqrt`), and $\delta$ is `deficitLog x y z t`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/AmplitudeDamping/ScalarDeficit.lean#L70-L89

import Mathlib
import Definitions.Def_AmplitudeDamping
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_Channel
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_MatrixDifferentiation
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_LogDetConvexity
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_LogDetEntropy
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_Pinching
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_GramMatrices
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_ScalarDeficit

open OAI OAI.GAD
universe u_1 u_2
open scoped BigOperators
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder
open scoped ComplexOrder MatrixOrder
open Matrix Set
open scoped ComplexOrder MatrixOrder
open scoped BigOperators Topology
open Filter Set
open scoped BigOperators ComplexOrder MatrixOrder Topology
open scoped BigOperators ComplexOrder
open Matrix Set

theorem OAI.GAD.deficitSpectrum_log {x y z t : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (ht : 0 < t) :
    ∑ i, deficitSigns i * Real.log (1 + deficitSpectrum x y z i / t) = deficitLog x y z t := by sorry
