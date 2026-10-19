-- Prove2me | Theorems.Thm_OAI_Barnette_BMatching_data_of_gadget
-- name    : OAI.Barnette.BMatching.data_of_gadget
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T02:45:46.806576+00:00
-- url     : https://prove2.me/theorems/8a6f8f62-d949-4898-b65b-ca291820a5de
-- title:
--   A perfect matching of the gadget yields a sub-relation of degree two on both sides
-- statement:
--   Let $A$ and $B$ be sets and $R\subseteq A\times B$ a relation, with set of incidences $I=\{(a,b)\in A\times B: (a,b)\in R\}$. The gadget of $R$ is the bipartite graph $\Gamma_R$ with left vertex set $\mathcal L=(A\times\{0,1\})\sqcup I$ and right vertex set $\mathcal R=(B\times\{0,1\})\sqcup I$, whose only edges are:
--
--   1. a left copy $(a,k)\in A\times\{0,1\}$ is adjacent to a right incidence $x\in I$ when the first coordinate of $x$ is $a$;
--   2. a left incidence $x\in I$ is adjacent to a right copy $(b,k)\in B\times\{0,1\}$ when the second coordinate of $x$ is $b$;
--   3. a left incidence $x$ is adjacent to the right incidence $y$ exactly when $x=y$.
--
--   There are no edges between left copies $(a,k)$ and right copies $(b,k')$.
--
--   **Theorem.** Let $A$ and $B$ be arbitrary sets. Suppose $\mu:\mathcal L\to\mathcal R$ is a bijection such that $\ell$ and $\mu(\ell)$ are adjacent in $\Gamma_R$ for every $\ell\in\mathcal L$, i.e. a perfect matching of the gadget. Then there exist injective maps $\lambda:A\times\{0,1\}\to I$ and $\kappa:B\times\{0,1\}\to I$ such that
--
--   $$\lambda(a,k)\in\{a\}\times B,\qquad \kappa(b,k)\in A\times\{b\},\qquad \lambda(A\times\{0,1\})=\kappa(B\times\{0,1\}).$$
--
--   Consequently the common image $M\subseteq R$ is a sub-relation in which every $a\in A$ lies in exactly two incidences, namely $\lambda(a,0)$ and $\lambda(a,1)$, and every $b\in B$ lies in exactly two incidences, namely $\kappa(b,0)$ and $\kappa(b,1)$. In graph terms $M$ is a spanning $2$-regular subgraph of the bipartite graph of $R$. Together with Hall's condition for the gadget, this converts a capacity condition on $R$ into such a $2$-factor, labeled at both sides.
--
--   **Formalization Note** The matching is an equivalence `f : Left R ≃ Right R` with `hf : ∀ l, gadget R l (f l)`, and the conclusion is `Nonempty (FactorData R)`. Here `FactorData R` has embeddings `left : A × Fin 2 ↪ Inc R` and `right : B × Fin 2 ↪ Inc R`, coordinate conditions `left_coord` and `right_coord`, and `same_range`. No finiteness of $A$ or $B$ is needed.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Hamiltonian/BMatching.lean#L161-L209

import Mathlib
import Definitions.Def_BarnetteHamiltonian
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Network
import Definitions.Def_OAI_Combinatorics_Hamiltonian_CutSpaces
import Definitions.Def_OAI_Combinatorics_Hamiltonian_FlowCircuits
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Bonds
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Quotients
import Definitions.Def_OAI_Combinatorics_Hamiltonian_DiskRegions
import Definitions.Def_OAI_Combinatorics_Hamiltonian_StateDisk
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Circulation
import Definitions.Def_OAI_Combinatorics_Hamiltonian_TriangleSystem
import Definitions.Def_OAI_Combinatorics_Hamiltonian_ColoredDual
import Definitions.Def_OAI_Combinatorics_Hamiltonian_CycleReversal
import Definitions.Def_OAI_Combinatorics_Hamiltonian_PairPhases
import Definitions.Def_OAI_Combinatorics_Hamiltonian_PairPolynomials
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Forest
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Contraction
import Definitions.Def_OAI_Combinatorics_Hamiltonian_MinorDuality
import Definitions.Def_OAI_Combinatorics_Hamiltonian_BMatching

open OAI OAI.Barnette OAI.Barnette.BMatching
open scoped Classical
variable {A B : Type*} [Fintype A] [Fintype B]

omit [Fintype A] [Fintype B] in
theorem OAI.Barnette.BMatching.data_of_gadget (R : A → B → Prop) (f : Left R ≃ Right R)
    (hf : ∀ l, gadget R l (f l)) : Nonempty (FactorData R) := by sorry
