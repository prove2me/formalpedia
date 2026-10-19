-- Prove2me | Theorems.Thm_OAI_BalancedTransport_Effectivity_rhoCoeffs_spec
-- name    : OAI.BalancedTransport.Effectivity.rhoCoeffs_spec
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T04:19:02.807773+00:00
-- url     : https://prove2.me/theorems/0fe475a5-c33d-47a1-9493-1358f5279a02
-- title:
--   The coefficient lists compute the derivative polynomials of $e^{-1/x}$
-- statement:
--   Let $P_0=1$ and $P_{n+1}(y)=y^2(P_n(y)-P_n'(y))$, so that the $n$-th derivative of $e^{-1/x}$ is $P_n(1/x)e^{-1/x}$ for $x>0$. Let the coefficient lists be defined by $L_0=[1]$ and $L_{n+1}=(0,0,c_0-c_1,c_1-2c_2,\dots)$ when $L_n=(c_0,c_1,\dots)$. Then for all $n,j$,
--   $$
--   L_n[j]=[y^j]\,P_n,
--   $$
--   where entries beyond the end of the list are read as $0$.
--
--   So the list recursion is a correct algorithm for the derivative polynomials.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/RhoAlgorithms.lean#L60-L73

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

theorem OAI.BalancedTransport.Effectivity.rhoCoeffs_spec (n j : ℕ) : (rhoCoeffs n).getD j 0 = (rhoPolynomial n).coeff j := by sorry
