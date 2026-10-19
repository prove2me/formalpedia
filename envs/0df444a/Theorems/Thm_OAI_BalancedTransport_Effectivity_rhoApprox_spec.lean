-- Prove2me | Theorems.Thm_OAI_BalancedTransport_Effectivity_rhoApprox_spec
-- name    : OAI.BalancedTransport.Effectivity.rhoApprox_spec
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T04:19:36.657281+00:00
-- url     : https://prove2.me/theorems/e2f1c3ee-6464-4dff-8f4f-5bbbc3879701
-- title:
--   Rational approximation of the derivatives of $e^{-1/x}$
-- statement:
--   Let $\rho(x)=e^{-1/x}$ for $x>0$ and $\rho(x)=0$ for $x\le0$. For $n\in\mathbb N$, rational $q$ and precision $p$, let $A(n,q,p)$ be $0$ if $q\le0$. Otherwise it is $P_n(1/q)$ times the rational approximation of $e^{-1/q}$ at precision $p+N$, where $N$ is the absolute value of the numerator of $P_n(1/q)$. Then
--   $$
--   \bigl|A(n,q,p)-\rho^{(n)}(q)\bigr|\le2^{-p}.
--   $$
--
--   This is the rational algorithm for the flat-function operation of numeric programs.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/RhoAlgorithms.lean#L184-L196

import Mathlib
import Definitions.Def_BalancedThreeStack
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_FlatBounds
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EffectiveArithmetic
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RationalAlgorithms
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EffectiveExp
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RecorderRules
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_PrefixCoding
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_BoxCoding
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Work
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_TimeRegularity
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_FieldBounds
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_CompactFamilies
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_ResidualRegularity
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RhoAlgorithms

open OAI OAI.BalancedTransport OAI.BalancedTransport.Effectivity
open Polynomial
open scoped NNReal

theorem OAI.BalancedTransport.Effectivity.rhoApprox_spec (n : ℕ) (q : ℚ) (p : ℕ) :
    |(rhoApprox n q p : ℝ) - rhoJet n (q : ℝ)| ≤ error p := by sorry
