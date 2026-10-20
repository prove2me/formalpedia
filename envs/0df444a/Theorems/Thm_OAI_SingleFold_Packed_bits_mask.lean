-- Prove2me | Theorems.Thm_OAI_SingleFold_Packed_bits_mask
-- name    : OAI.SingleFold.Packed.bits_mask
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T17:30:26.729262+00:00
-- url     : https://prove2.me/theorems/a2e07f85-eeb4-462c-bd09-e725e5801043
-- title:
--   Domination by a repeated digit mask controls each block
-- statement:
--   Write $x\preceq y$ if every binary digit of $x$ is at most the corresponding binary digit of $y$. For $B,k\in\mathbb{N}$ write $\mathrm{digit}_B(x,t)=\lfloor x/B^t\rfloor\bmod B$, $\mathrm{pack}_B(k,f)=\sum_{t<k}f(t)B^t$ and $\mathrm{ones}_B(k)=\mathrm{pack}_B(k,1)$. Let $w>0$ and $c<2^w$, and put $B=2^w$. Then
--   $$
--   x\preceq c\cdot\mathrm{ones}_B(k)\iff x<B^k\ \text{ and }\ \mathrm{digit}_B(x,t)\preceq c\ \text{ for all }t<k .
--   $$
--
--   With a power-of-two base the base-$B$ digits are aligned blocks of $w$ bits, so a single domination imposes a bound on every digit at once.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/SingleFold/Packed.lean#L153-L172

import Mathlib
import Definitions.Def_SingleFold
import Definitions.Def_OAI_NumberTheory_SingleFold_PolynomialCompiler
import Definitions.Def_OAI_NumberTheory_SingleFold_RationalCodes
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticCoordinates
import Definitions.Def_OAI_NumberTheory_SingleFold_FunctionalCompiler
import Definitions.Def_OAI_NumberTheory_SingleFold_DescentMap
import Definitions.Def_OAI_NumberTheory_SingleFold_SquareSupport
import Definitions.Def_OAI_NumberTheory_SingleFold_LocalDescent
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticHeight
import Definitions.Def_OAI_NumberTheory_SingleFold_QuadraticHeight
import Definitions.Def_OAI_NumberTheory_SingleFold_FiniteGeneration
import Definitions.Def_OAI_NumberTheory_SingleFold_Rank
import Definitions.Def_OAI_NumberTheory_SingleFold_Duplication
import Definitions.Def_OAI_NumberTheory_SingleFold_Torsion
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticGrowth
import Definitions.Def_OAI_NumberTheory_SingleFold_Pell
import Definitions.Def_OAI_NumberTheory_SingleFold_Power
import Definitions.Def_OAI_NumberTheory_SingleFold_Binary
import Definitions.Def_OAI_NumberTheory_SingleFold_Packed

open OAI OAI.SingleFold OAI.SingleFold.Packed

theorem OAI.SingleFold.Packed.bits_mask {w k c x : ℕ} (hw : 0 < w) (hc : c < 2^w) :
    Bits x (c*ones (2^w) k) ↔ x < (2^w)^k ∧ ∀t < k, Bits (digit (2^w) x t) c := by sorry
