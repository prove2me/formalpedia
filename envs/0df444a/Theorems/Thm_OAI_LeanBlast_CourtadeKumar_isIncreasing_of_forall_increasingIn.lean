-- Prove2me | Theorems.Thm_OAI_LeanBlast_CourtadeKumar_isIncreasing_of_forall_increasingIn
-- name    : OAI.LeanBlast.CourtadeKumar.isIncreasing_of_forall_increasingIn
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T10:56:15.215644+00:00
-- url     : https://prove2.me/theorems/465f8df5-c69b-4c4b-8c0c-05cdd730a27e
-- title:
--   A function on the cube increasing in each coordinate is monotone
-- statement:
--   Let $F:\{0,1\}^n\to\mathbb{R}$. Suppose that for every coordinate $i$ and every $x$, $F(x^{i\to0})\le F(x^{i\to1})$, where $x^{i\to b}$ sets coordinate $i$ to $b$. Then $F$ is monotone: for all $x,y$,
--   $$
--   x\le y\ \text{coordinatewise}\ \Longrightarrow\ F(x)\le F(y).
--   $$
--
--   After every coordinate has been sorted, the rearranged function is monotone. This is the reduction of the Courtade–Kumar problem to increasing functions.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/BooleanNoise/Rearrangement.lean#L86-L105

import Mathlib
import Definitions.Def_CourtadeKumar
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Model__CourtadeKumar
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Statement__CourtadeKumar
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Basic
import Definitions.Def_OAI_InformationTheory_BooleanNoise_FiniteNoise
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Statement
import Definitions.Def_OAI_InformationTheory_BooleanNoise_EntropyScalars
import Definitions.Def_OAI_InformationTheory_BooleanNoise_FiniteDistribution
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Attainment
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Rearrangement

open OAI OAI.LeanBlast OAI.LeanBlast.CourtadeKumar
open scoped BigOperators
variable {n : ℕ}

theorem OAI.LeanBlast.CourtadeKumar.isIncreasing_of_forall_increasingIn {F : Cube n → ℝ}
    (hF : ∀ i, IsIncreasingIn i F) : IsIncreasing F := by sorry
