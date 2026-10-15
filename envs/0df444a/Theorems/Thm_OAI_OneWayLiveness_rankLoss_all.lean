-- Prove2me | Theorems.Thm_OAI_OneWayLiveness_rankLoss_all
-- name    : OAI.OneWayLiveness.rankLoss_all
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T04:27:04.682499+00:00
-- url     : https://prove2.me/theorems/e4c71f70-53c4-4e11-bc88-4f0e189406f4
-- title:
--   Exponential rank loss for Brauer-monoid representations of relation monoids with unit lifts
-- statement:
--   Let $\mathcal R_H$ denote the monoid of all binary relations on a set $H$, with product $RS=\{(x,z):\ (x,y)\in R \text{ and } (y,z)\in S \text{ for some } y\}$ (composition in diagrammatic order) and identity the diagonal $\Delta_H$. For $F\subseteq H$ write $\Delta_F=\{(z,z): z\in F\}$, and for $x,y\in H$ write $E_{x,y}=\Delta_H\cup\{(x,y)\}$ for the identity relation with one extra pair.
--
--   For a finite set $A$, let $\mathcal B_A$ be the Brauer monoid of $A$: an element is a perfect matching of the $2|A|$ ports $i_{\mathrm L},i_{\mathrm R}$ ($i\in A$), drawn with the left ports on one side and the right ports on the other; the product $\pi\sigma$ glues the right ports of $\pi$ to the left ports of $\sigma$, follows the resulting paths and discards closed loops, and the identity matches each $i_{\mathrm L}$ with $i_{\mathrm R}$. The rank $\operatorname{rk}\pi$ is the number of through strands, i.e. of $i\in A$ whose left port $i_{\mathrm L}$ is matched to some right port, and the support $\operatorname{supp}\pi$ is the set of $i\in A$ such that $i_{\mathrm L}$ is not matched to $i_{\mathrm R}$.
--
--   For every $h\in\mathbb N$ the following holds. Let $H$ be a finite set with $|H|=h$, let $A$ be a finite set and $M$ a finite monoid, let $\rho\colon M\to\mathcal B_A$ be an injective homomorphism, and let $\varphi\colon M\to\mathcal R_H$ be a surjective homomorphism with unit lifts (every unit of $\mathcal R_H$, i.e. every permutation graph, is $\varphi(u)$ for a unit $u$ of $M$). If $a\in M$ is idempotent and $\varphi(a)=E_{x,y}$ for some $x\neq y$ in $H$, then
--
--   $$2^{\lfloor (h-2)/31\rfloor}\le |A|-\operatorname{rk}\rho(a).$$
--
--   The right-hand side is the rank defect of $\rho(a)$: the number of points of $A$ that are not left endpoints of through strands. The theorem says that a faithful representation by matching diagrams of a finite monoid mapping onto all relations on $h$ points, with liftable permutations, loses exponentially many through strands at every idempotent that represents a single extra pair. It is the core of the lower bound $|A|\ge 2^{\lfloor (h-2)/31\rfloor}$ whenever $\mathcal R_H$ is a homomorphic image of a submonoid of $\mathcal B_A$.
--
--   **Formalization Note** The statement is `RankLossAt h`, which quantifies over types `H A M : Type` with `Fintype`/`Finite` instances; $2^{\lfloor (h-2)/31\rfloor}$ is `rankLoss h`, computed with natural-number subtraction and division, so the bound is $1\le|A|-\operatorname{rk}\rho(a)$ for all $h\le 32$. The subtraction $|A|-\operatorname{rk}\rho(a)$ is also in $\mathbb N$, which is harmless because $\operatorname{rk}\rho(a)\le|A|$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Automata/RankLoss.lean#L274-L351

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

theorem OAI.OneWayLiveness.rankLoss_all (h : ℕ) : RankLossAt h := by sorry
