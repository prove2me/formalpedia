-- Prove2me | Theorems.Thm_OAI_QAC_list_conjugate_filter
-- name    : OAI.QAC.list_conjugate_filter
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T00:37:57.575254+00:00
-- url     : https://prove2.me/theorems/ebec3056-d907-4b66-a0e6-c8059ff4fd1c
-- title:
--   Commuting unitaries that commute with $B$ drop out of a conjugation
-- statement:
--   Let $\mathcal A$ be a unital $C^{*}$-algebra and write $\operatorname{conj}_U(B)=UBU^{*}$. Let $f:\iota\to\mathcal A$, let $l=(a_1,\dots,a_n)$ be a list of elements of $\iota$, let $p:\iota\to\{\mathrm{true},\mathrm{false}\}$ be a predicate, and let $B\in\mathcal A$. Assume:
--
--   1. the elements $f(a_j)$ pairwise commute: $f(a_j)f(a_k)=f(a_k)f(a_j)$ for all positions $j<k$;
--   2. every $f(a_j)$ is unitary;
--   3. every $f(a_j)$ with $p(a_j)=\mathrm{false}$ commutes with $B$.
--
--   Then, with ordered products $f(a_1)f(a_2)\cdots f(a_n)$,
--   $$
--   \operatorname{conj}_{f(a_1)f(a_2)\cdots f(a_n)}(B)=\operatorname{conj}_{\prod_{j:\,p(a_j)=\mathrm{true}}f(a_j)}(B),
--   $$
--   where on the right the product is taken over the entries with $p(a_j)=\mathrm{true}$, in their original order.
--
--   In the circuit setting the $f(a_j)$ are the reflections $I-2P^0_{D_j}$ of a parallel layer, which pairwise commute because their supports are disjoint, and $B=P_A^0$ is a product projection. The lemma shows that conjugating $P_A^0$ by the whole layer is the same as conjugating it by the sublayer of gates whose support meets the support of $A$.
--
--   **Formalization Note** The products are `List.prod` of `l.map f` and of `(l.filter p).map f`, the conjugation is `conjugate U B = U * B * star U`, and unitarity is membership in `unitary A`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/QuantumCircuit/Transition.lean#L208-L232

import Mathlib
import Definitions.Def_QACParity
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Basic
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_ProductProjection
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Circuit
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Count
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Spectral
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Transition

open OAI OAI.QAC
open scoped BigOperators Matrix.Norms.L2Operator symmDiff
open Matrix
variable {A : Type*} [CStarAlgebra A]

theorem OAI.QAC.list_conjugate_filter {ι : Type*} (f : ι → A) (l : List ι) (p : ι → Bool) (B : A)
    (hl : l.Pairwise (fun a b => Commute (f a) (f b)))
    (hu : ∀ a ∈ l, f a ∈ unitary A)
    (hd : ∀ a ∈ l, p a = false → Commute (f a) B) :
    conjugate (l.map f).prod B = conjugate ((l.filter p).map f).prod B := by sorry
