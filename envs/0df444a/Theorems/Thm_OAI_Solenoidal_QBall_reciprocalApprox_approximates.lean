-- Prove2me | Theorems.Thm_OAI_Solenoidal_QBall_reciprocalApprox_approximates
-- name    : OAI.Solenoidal.QBall.reciprocalApprox_approximates
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T01:48:26.819974+00:00
-- url     : https://prove2.me/theorems/ae1c8301-7b30-4b73-913b-d75fdfae7046
-- title:
--   Rational interval approximation of $1/(\psi(q)+\psi(1-q))$ at rational points
-- statement:
--   A *rational ball* is a pair $(c,r)\in\mathbb{Q}^2$; it *contains* $x\in\mathbb{R}$ if $|c-x|\le r$. A sequence of balls $(c_n,r_n)_{n\in\mathbb{N}}$ *approximates* $x$ if every ball contains $x$ and $r_n\to0$. Ball arithmetic is
--   $$\mathrm{pt}(q)=(q,0),\quad (c,r)+(c',r')=(c+c',\,r+r'),\quad (c,r)\cdot(c',r')=(cc',\;|c|r'+|c'|r+rr'),$$
--   with powers $B^0=\mathrm{pt}(1)$, $B^{k+1}=B^k\cdot B$. For $q\in\mathbb{Q}$ and $n\in\mathbb{N}$ define
--   $$\mathrm{sexp}(q,n)=\Big(\sum_{k=0}^{n}\frac{q^k}{k!},\;2\cdot2^{-(n+1)}\Big),\qquad K(q)=2\,(|\mathrm{num}(q)|+1),\qquad \mathcal{E}(q,n)=\mathrm{sexp}\big(q/K(q),n\big)^{K(q)},$$
--   where $\mathrm{num}(q)$ is the numerator of $q$ in lowest terms; further $\Phi(q,n)=\mathrm{pt}(0)$ if $q\le0$ and $\Phi(q,n)=\mathrm{pt}(1)\cdot\mathcal{E}(-1/q,n)$ if $q>0$; $\mathrm{clinv}(c,r)=\big(1/\max(\tfrac1{32},c),\;512\,r\big)$; and finally
--   $$\mathrm{recip}(q,n)=\mathrm{clinv}\big(\Phi(q,n)+\Phi(1-q,n)\big).$$
--
--   Let $\psi(x)=e^{-1/x}$ for $x>0$ and $\psi(x)=0$ for $x\le0$, and $\rho(x)=1/\big(\psi(x)+\psi(1-x)\big)$.
--
--   **Theorem.** For every $q\in\mathbb{Q}$ the sequence $n\mapsto\mathrm{recip}(q,n)$ approximates $\rho(q)$:
--
--   $$
--   \big|\,c_n(q)-\rho(q)\,\big|\le r_n(q)\ \text{ for all } n,\qquad r_n(q)\to0,\qquad\text{where } (c_n(q),r_n(q))=\mathrm{recip}(q,n).
--   $$
--
--   The balls are produced from $(q,n)$ by finitely many exact rational operations, so this gives an algorithm that computes $\rho$ at rational points to any prescribed accuracy, with a certified error bound. Together with the analogous approximations of the flat functions it is the basis for evaluating the smooth step $S=\psi\rho$ and the profiles built from it effectively.
--
--   **Formalization Note** Balls are `QBall := ℚ × ℚ`, approximation is the structure `QBall.Approximates`, $\mathrm{sexp}$, $K$, $\mathcal{E}$, $\Phi$, $\mathrm{clinv}$, $\mathrm{recip}$ are `smallExp`, `expScale`, `expApprox`, `flatApprox 0`, `clampInv`, `reciprocalApprox`, and $\rho$ is `transitionReciprocal`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/SheetFlows/RationalBalls.lean#L223-L235

import Mathlib
import Definitions.Def_SolenoidalSheetPrograms
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_DirectForce
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Profiles
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Clocks
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Differential
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_ScheduledForce
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_ClassicalRegularity
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_EnergyIdentities
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_RectangleGeometry
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Trajectories
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Pulses
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Localization
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_ShearCore
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Routing
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_JetCalculus
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_JetProfiles
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_BoxJets
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_RationalFormula
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_FormulaProfiles
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_RationalBalls

open OAI OAI.Solenoidal OAI.Solenoidal.QBall
open Set Filter
open scoped Topology BigOperators

theorem OAI.Solenoidal.QBall.reciprocalApprox_approximates (q : ℚ) :
    Approximates (reciprocalApprox q) (transitionReciprocal (q:ℝ)) := by sorry
