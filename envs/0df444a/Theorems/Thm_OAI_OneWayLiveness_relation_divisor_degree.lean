-- Prove2me | Theorems.Thm_OAI_OneWayLiveness_relation_divisor_degree
-- name    : OAI.OneWayLiveness.relation_divisor_degree
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T04:27:45.071239+00:00
-- url     : https://prove2.me/theorems/998d1e42-0dc6-4498-99ba-938c7ef30913
-- title:
--   If the full relation monoid on $h$ points divides the Brauer monoid of $A$, then $|A|\ge 2^{\lfloor (h-2)/31\rfloor}$
-- statement:
--   Let $\mathcal R_H$ denote the monoid of all binary relations on a set $H$, with product $RS=\{(x,z):\ (x,y)\in R \text{ and } (y,z)\in S \text{ for some } y\}$ (composition in diagrammatic order) and identity the diagonal $\Delta_H$. For $F\subseteq H$ write $\Delta_F=\{(z,z): z\in F\}$, and for $x,y\in H$ write $E_{x,y}=\Delta_H\cup\{(x,y)\}$ for the identity relation with one extra pair.
--
--   For a finite set $A$, let $\mathcal B_A$ be the Brauer monoid of $A$: an element is a perfect matching of the $2|A|$ ports $i_{\mathrm L},i_{\mathrm R}$ ($i\in A$), drawn with the left ports on one side and the right ports on the other; the product $\pi\sigma$ glues the right ports of $\pi$ to the left ports of $\sigma$, follows the resulting paths and discards closed loops, and the identity matches each $i_{\mathrm L}$ with $i_{\mathrm R}$. The rank $\operatorname{rk}\pi$ is the number of through strands, i.e. of $i\in A$ whose left port $i_{\mathrm L}$ is matched to some right port, and the support $\operatorname{supp}\pi$ is the set of $i\in A$ such that $i_{\mathrm L}$ is not matched to $i_{\mathrm R}$.
--
--   Let $H$ and $A$ be finite sets such that $H$ contains two distinct elements $x\neq y$. Let $M$ be a finite monoid, $\rho\colon M\to\mathcal B_A$ an injective homomorphism and $\varphi\colon M\to\mathcal R_H$ a surjective homomorphism. Then
--
--   $$2^{\lfloor (|H|-2)/31\rfloor}\le |A|.$$
--
--   In the language of finite semigroup theory: if the monoid of all binary relations on $h\ge2$ points divides the Brauer monoid $\mathcal B_A$ (is a homomorphic image of a submonoid of it), then $|A|\ge2^{\lfloor (h-2)/31\rfloor}$, so the number of points must grow exponentially with $h$. Unlike the rank-loss theorem, no hypothesis about lifting permutations is needed.
--
--   **Formalization Note** The types $H,A,M$ live in `Type`; $\mathcal B_A$ is `Pairing (A ⊕ A)` and $\mathcal R_H$ is `BRel H`. The left-hand side is `rankLoss (Fintype.card H)`, computed with natural-number subtraction and division.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Automata/RankLoss.lean#L364-L382

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
import Definitions.Def_OAI_Combinatorics_Automata_RankLoss

open OAI OAI.OneWayLiveness
open scoped Classical

theorem OAI.OneWayLiveness.relation_divisor_degree {H A M : Type} [Fintype H] [Fintype A]
    [Monoid M] [Finite M] (ρ : M →* Pairing (A ⊕ A)) (hρ : Function.Injective ρ)
    (φ : M →* BRel H) (hφ : Function.Surjective φ) (x y : H) (hxy : x ≠ y) :
    rankLoss (Fintype.card H) ≤ Fintype.card A := by sorry
