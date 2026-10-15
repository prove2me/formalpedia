-- Prove2me | Theorems.Thm_OAI_OneWayLiveness_conjugate_lift
-- name    : OAI.OneWayLiveness.conjugate_lift
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T04:20:42.637979+00:00
-- url     : https://prove2.me/theorems/84dbf75a-dd12-4e59-8a16-406007468f49
-- title:
--   Conjugating an idempotent one-pair lift to any other pair without changing its rank
-- statement:
--   Let $\mathcal R_H$ denote the monoid of all binary relations on a set $H$, with product $RS=\{(x,z):\ (x,y)\in R \text{ and } (y,z)\in S \text{ for some } y\}$ (composition in diagrammatic order) and identity the diagonal $\Delta_H$. For $F\subseteq H$ write $\Delta_F=\{(z,z): z\in F\}$, and for $x,y\in H$ write $E_{x,y}=\Delta_H\cup\{(x,y)\}$ for the identity relation with one extra pair.
--
--   For a finite set $A$, let $\mathcal B_A$ be the Brauer monoid of $A$: an element is a perfect matching of the $2|A|$ ports $i_{\mathrm L},i_{\mathrm R}$ ($i\in A$), drawn with the left ports on one side and the right ports on the other; the product $\pi\sigma$ glues the right ports of $\pi$ to the left ports of $\sigma$, follows the resulting paths and discards closed loops, and the identity matches each $i_{\mathrm L}$ with $i_{\mathrm R}$. The rank $\operatorname{rk}\pi$ is the number of through strands, i.e. of $i\in A$ whose left port $i_{\mathrm L}$ is matched to some right port, and the support $\operatorname{supp}\pi$ is the set of $i\in A$ such that $i_{\mathrm L}$ is not matched to $i_{\mathrm R}$.
--
--   Let $H$ be a finite set, $A$ a finite set and $M$ a monoid, and let $\rho\colon M\to\mathcal B_A$ and $f\colon M\to\mathcal R_H$ be monoid homomorphisms. Assume that $f$ has unit lifts: every unit of $\mathcal R_H$ (the graph of a permutation of $H$) equals $f(w)$ for some unit $w$ of $M$. Let $a\in M$ be idempotent with $f(a)=E_{x,y}$ for some $x\neq y$ in $H$. Then for every pair $u\neq v$ in $H$ there exists $b\in M$ with
--
--   $$b^2=b,\qquad f(b)=E_{u,v},\qquad \operatorname{rk}\rho(b)=\operatorname{rk}\rho(a).$$
--
--   Thus one idempotent lift of a single extra pair can be moved to any other off-diagonal pair at no cost in diagram rank. In the exponential rank-loss argument this supplies, from one hypothesised generator, idempotent lifts of all the single-pair relations needed to assemble larger relations, each with the same rank defect.
--
--   **Formalization Note** $\mathcal B_A$ is `Pairing (A ⊕ A)` with the product `Pairing.compose`, $\mathcal R_H$ is `BRel H`, $E_{x,y}$ is `BRel.addEdge x y` and the unit-lift hypothesis is `HasUnitLifts f`. The monoid $M$ is not assumed finite and $\rho$ is not assumed injective.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Automata/Relations.lean#L165-L180

import Mathlib
import Definitions.Def_OneWayLiveness
import Definitions.Def_OAI_Combinatorics_Automata_Model
import Definitions.Def_OAI_Combinatorics_Automata_Wiring
import Definitions.Def_OAI_Combinatorics_Automata_Cells
import Definitions.Def_OAI_Combinatorics_Automata_Tours
import Definitions.Def_OAI_Combinatorics_Automata_Normalization
import Definitions.Def_OAI_Combinatorics_Automata_Network
import Definitions.Def_OAI_Combinatorics_Automata_Rank
import Definitions.Def_OAI_Combinatorics_Automata_Diagram
import Definitions.Def_OAI_Combinatorics_Automata_Diagrams
import Definitions.Def_OAI_Combinatorics_Automata_Corners
import Definitions.Def_OAI_Combinatorics_Automata_Relations

open OAI OAI.OneWayLiveness

theorem OAI.OneWayLiveness.conjugate_lift {M H A : Type*} [Monoid M] [Finite H] [Fintype A]
    (ρ : M →* Pairing (A ⊕ A)) (f : M →* BRel H) (hl : HasUnitLifts f)
    (a : M) (ha : a * a = a) (x y : H) (hxy : x ≠ y) (hfa : f a = BRel.addEdge x y)
    (u v : H) (huv : u ≠ v) :
    ∃ b : M, b * b = b ∧ f b = BRel.addEdge u v ∧ Pairing.rank (ρ b) = Pairing.rank (ρ a) := by sorry
