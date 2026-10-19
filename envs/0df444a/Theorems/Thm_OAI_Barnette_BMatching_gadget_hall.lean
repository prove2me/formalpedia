-- Prove2me | Theorems.Thm_OAI_Barnette_BMatching_gadget_hall
-- name    : OAI.Barnette.BMatching.gadget_hall
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T02:45:13.540404+00:00
-- url     : https://prove2.me/theorems/176b876a-3beb-41d1-b8cd-c2dfed55f94a
-- title:
--   Hall's condition for the matching gadget of a relation with capacity two
-- statement:
--   Let $A$ and $B$ be sets and $R\subseteq A\times B$ a relation, with set of incidences $I=\{(a,b)\in A\times B: (a,b)\in R\}$. The gadget of $R$ is the bipartite graph $\Gamma_R$ with left vertex set $\mathcal L=(A\times\{0,1\})\sqcup I$ and right vertex set $\mathcal R=(B\times\{0,1\})\sqcup I$, whose only edges are:
--
--   1. a left copy $(a,k)\in A\times\{0,1\}$ is adjacent to a right incidence $x\in I$ when the first coordinate of $x$ is $a$;
--   2. a left incidence $x\in I$ is adjacent to a right copy $(b,k)\in B\times\{0,1\}$ when the second coordinate of $x$ is $b$;
--   3. a left incidence $x$ is adjacent to the right incidence $y$ exactly when $x=y$.
--
--   There are no edges between left copies $(a,k)$ and right copies $(b,k')$. For $S\subseteq\mathcal L$ let $\Gamma_R(S)\subseteq\mathcal R$ be the set of right vertices adjacent to some vertex of $S$.
--
--   **Theorem.** Let $A$ and $B$ be finite. Suppose that for every $S\subseteq A$
--
--   $$2\,|S|\ \le\ \sum_{b\in B}\min\big(2,\ |\{a\in S:(a,b)\in R\}|\big).$$
--
--   Then Hall's condition holds for the gadget: $|\mathcal S|\le|\Gamma_R(\mathcal S)|$ for every set $\mathcal S\subseteq\mathcal L$ of left vertices.
--
--   The hypothesis is the capacity condition for selecting, inside $R$, exactly two incidences at every $a\in A$ with at most two at every $b\in B$. By Hall's marriage theorem the conclusion yields a matching of $\Gamma_R$ that covers every left vertex. When $|A|=|B|$ the two sides have the same size $2|A|+|I|$, so such a matching is a bijection $\mathcal L\to\mathcal R$ along edges of $\Gamma_R$. The companion result on gadget matchings turns this into a $2$-regular sub-relation of $R$.
--
--   **Formalization Note** The gadget is `gadget R : Left R → Right R → Prop` with `Left R = (A × Fin 2) ⊕ Inc R` and `Right R = (B × Fin 2) ⊕ Inc R`, where `Inc R` is the subtype of incidences. The neighborhood is `Finset.univ.filter fun r => ∃ l ∈ L, gadget R l r`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Hamiltonian/BMatching.lean#L45-L136

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

theorem OAI.Barnette.BMatching.gadget_hall (R : A → B → Prop)
    (hcap : ∀ S : Finset A, 2*S.card ≤ ∑ b, min 2 ((S.filter fun a => R a b).card))
    (L : Finset (Left R)) :
    L.card ≤ (Finset.univ.filter fun r : Right R => ∃ l ∈ L, gadget R l r).card := by sorry
