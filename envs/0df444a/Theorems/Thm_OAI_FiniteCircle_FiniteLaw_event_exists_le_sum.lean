-- Prove2me | Theorems.Thm_OAI_FiniteCircle_FiniteLaw_event_exists_le_sum
-- name    : OAI.FiniteCircle.FiniteLaw.event_exists_le_sum
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T14:19:13.939435+00:00
-- url     : https://prove2.me/theorems/247bbe9d-cf84-44b9-98e0-bfd5b752ce63
-- title:
--   Union bound for finite probability laws
-- statement:
--   A *finite probability law* $\mu$ on a finite set $\Omega$ is a weight function $\mu:\Omega\to\mathbb{R}$ with $\mu(\omega)\ge0$ for all $\omega$ and $\sum_{\omega\in\Omega}\mu(\omega)=1$. The probability of a property $P$ of the points of $\Omega$ is $\mu(P)=\sum_{\omega:\,P(\omega)}\mu(\omega)$.
--
--   **Theorem (union bound).** Let $\mu$ be a finite probability law on $\Omega$, let $\iota$ be a finite index set, and let $(P_i)_{i\in\iota}$ be properties of the points of $\Omega$. Then
--
--   $$
--   \mu\bigl(\{\omega\in\Omega:\ P_i(\omega)\text{ holds for some }i\in\iota\}\bigr)\ \le\ \sum_{i\in\iota}\mu(P_i).
--   $$
--
--   This is Boole's inequality in the elementary setting of finitely many weighted outcomes, the probability framework used for the random partitions and random labellings in the construction of $\ell^1$ embeddings of edit distance. It is used, for example, to show that with probability at least $1/2$ no window of one word receives the same random label as any window of another word.
--
--   **Formalization Note** The law is the structure `FiniteLaw Ω` (fields `weight`, `nonneg`, `total`) on a type with a `Fintype` instance, and `μ.event P` is the sum of the weights of the points satisfying `P`, defined using classical decidability.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/FiniteCircle/Partitions.lean#L94-L107

import Mathlib
import Definitions.Def_FiniteCircle
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Model
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Edit
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Matching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_TaggedRows
import Definitions.Def_OAI_Combinatorics_FiniteCircle_PhaseCost
import Definitions.Def_OAI_Combinatorics_FiniteCircle_CircleWords
import Definitions.Def_OAI_Combinatorics_FiniteCircle_MaskSeparation
import Definitions.Def_OAI_Combinatorics_FiniteCircle_ExcludedSeparation
import Definitions.Def_OAI_Combinatorics_FiniteCircle_MaskDescent
import Definitions.Def_OAI_Combinatorics_FiniteCircle_ExcludedDescent
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Primes
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Fourier
import Definitions.Def_OAI_Combinatorics_FiniteCircle_DyadicShifts
import Definitions.Def_OAI_Combinatorics_FiniteCircle_MaskBranching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_TreeBranching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Translations
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Distortion
import Definitions.Def_OAI_Combinatorics_FiniteCircle_BlockMatching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_OffsetRecovery
import Definitions.Def_OAI_Combinatorics_FiniteCircle_RandomCodes
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Codes
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Lower
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Windows
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Partitions

open OAI OAI.FiniteCircle OAI.FiniteCircle.FiniteLaw
open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module
open Classical
variable {Ω : Type*} [Fintype Ω]

theorem OAI.FiniteCircle.FiniteLaw.event_exists_le_sum {ι : Type*} [Fintype ι] (μ : FiniteLaw Ω) (P : ι → Ω → Prop) :
    μ.event (fun ω => ∃ i, P i ω) ≤ ∑ i, μ.event (P i) := by sorry
