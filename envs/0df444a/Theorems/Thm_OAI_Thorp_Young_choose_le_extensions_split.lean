-- Prove2me | Theorems.Thm_OAI_Thorp_Young_choose_le_extensions_split
-- name    : OAI.Thorp.Young.choose_le_extensions_split
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T04:27:39.215243+00:00
-- url     : https://prove2.me/theorems/1f123864-bbbc-45c6-8c0e-7130f82e703f
-- title:
--   A poset split into two mutually incomparable parts has at least $\binom{|A|}{|s|}$ linear extensions
-- statement:
--   Let $A$ be a finite partially ordered set with $N=|A|$ elements. A *linear extension* of $A$ is a bijection $\lambda:A\to\{0,1,\dots,N-1\}$ that is strictly order-preserving: $x<y$ implies $\lambda(x)<\lambda(y)$. Write $e(A)$ for the number of linear extensions of $A$; a subset of $A$ is regarded as a poset with the induced order. Let $s\subseteq A$ be a subset such that no element of $s$ is comparable with an element outside $s$; precisely, for all $x,y\in A$ with $x<y$ we have $x\in s$ if and only if $y\in s$. Then
--
--   $$
--   \binom{|A|}{|s|}\le e(A).
--   $$
--
--   The hypothesis says that $A$ is the disjoint union of the two posets $s$ and $A\setminus s$ with no relations between them, and the bound counts only the ways of interleaving the two parts (the exact count is $\binom{|A|}{|s|}e(s)\,e(A\setminus s)$). It is the combinatorial input for lower bounds on the number of standard Young tableaux of a diagram with a long first row, where cells of that row far to the right are incomparable with the cells below it.
--
--   **Formalization Note** $e(A)$ is `Fintype.card (Extensions A)`, the number of `StrictMono` equivalences `A ≃ Fin (Fintype.card A)`; $\binom{N}{k}$ is `Nat.choose N k`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThorpShuffle/ExtensionBounds.lean#L93-L150

import Mathlib
import Definitions.Def_ThorpFirstReciprocal
import Definitions.Def_OAI_Probability_ThorpShuffle_Model
import Definitions.Def_OAI_Probability_ThorpShuffle_PairAveraging
import Definitions.Def_OAI_Probability_ThorpShuffle_Walsh
import Definitions.Def_OAI_Probability_ThorpShuffle_Support
import Definitions.Def_OAI_Probability_ThorpShuffle_ConditionalFlow
import Definitions.Def_OAI_Probability_ThorpShuffle_FiniteExpectation
import Definitions.Def_OAI_Probability_ThorpShuffle_WalshFlow
import Definitions.Def_OAI_Probability_ThorpShuffle_FreshCoins
import Definitions.Def_OAI_Probability_ThorpShuffle_HalfHistories
import Definitions.Def_OAI_Probability_ThorpShuffle_NoiseEnergy
import Definitions.Def_OAI_Probability_ThorpShuffle_EnergyDecay
import Definitions.Def_OAI_Probability_ThorpShuffle_MarginalEnergy
import Definitions.Def_OAI_Probability_ThorpShuffle_ConditionalLaw
import Definitions.Def_OAI_Probability_ThorpShuffle_TaggedCompletion
import Definitions.Def_OAI_Probability_ThorpShuffle_Reachability
import Definitions.Def_OAI_Probability_ThorpShuffle_Cyclic
import Definitions.Def_OAI_Probability_ThorpShuffle_Tableaux
import Definitions.Def_OAI_Probability_ThorpShuffle_Specht
import Definitions.Def_OAI_Probability_ThorpShuffle_Polytabloids
import Definitions.Def_OAI_Probability_ThorpShuffle_Irreducibility
import Definitions.Def_OAI_Probability_ThorpShuffle_Classification
import Definitions.Def_OAI_Probability_ThorpShuffle_LinearExtensions
import Definitions.Def_OAI_Probability_ThorpShuffle_ExtensionBounds

open OAI OAI.Thorp OAI.Thorp.Young
universe uA
open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter
open scoped Classical
variable {A : Type uA} [Fintype A] [PartialOrder A]

theorem OAI.Thorp.Young.choose_le_extensions_split (s : Set A)
    (hs : ∀ x y : A, x < y → (x ∈ s ↔ y ∈ s)) :
    (Fintype.card A).choose (Fintype.card s) ≤ Fintype.card (Extensions A) := by sorry
