-- Prove2me | Theorems.Thm_OAI_OneWayLiveness_min_rank_corner_isUnit
-- name    : OAI.OneWayLiveness.min_rank_corner_isUnit
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T04:19:02.640638+00:00
-- url     : https://prove2.me/theorems/353ebad1-dd09-4c72-9600-b79e91d84120
-- title:
--   For a minimum-rank idempotent lift, the restricted corner homomorphism reflects units
-- statement:
--   Let $M$ be a finite monoid, $N$ a monoid and $A$ a finite set. Let $\mathcal P(A)$ be the monoid of diagrams on $A$ (perfect matchings of $A\sqcup A$, multiplied by gluing), with $\operatorname{rank}$ the number of through-strands. Let $\rho:M\to\mathcal P(A)$ be an injective monoid homomorphism and let $\phi:M\to N$ be a monoid homomorphism. Let $e\in M$ and $q\in N$ be idempotents with $\phi(e)=q$, and assume that $e$ has minimum rank among the idempotent lifts of $q$:
--   $$
--   \operatorname{rank}\rho(e)\ \le\ \operatorname{rank}\rho(z)\qquad\text{for every } z\in M \text{ with } z^2=z \text{ and } \phi(z)=q .
--   $$
--   The corners $eMe=\{x\in M: ex=x=xe\}$ and $qNq$ are monoids with identities $e$ and $q$. Let $\phi_e:eMe\to qNq$ be the restriction of $\phi$.
--
--   **Theorem.** If $y\in eMe$ and $\phi_e(y)$ is a unit of $qNq$, then $y$ is a unit of $eMe$.
--
--   In other words, for an idempotent lift of minimum rank, the restricted homomorphism $\phi_e$ reflects units. In the rank-loss argument this is combined with the separate fact that $\phi_e$ is onto when $\phi$ is, to show that $\phi_e$ has unit lifts. This lets the rank-loss induction pass to the corner at $e$ while keeping the unit-lift hypothesis for the induced map onto the relation monoid.
--
--   **Formalization Note** The corner is `Corner e he`, the restricted map is `Corner.mapTo f hf`, and both the hypothesis and the conclusion use `IsUnit` in the corner monoids. The universes of $M$, $N$ and $A$ are arbitrary.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Automata/Corners.lean#L152-L176

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

open OAI OAI.OneWayLiveness

theorem OAI.OneWayLiveness.min_rank_corner_isUnit {M N A : Type*} [Monoid M] [Monoid N] [Finite M] [Fintype A]
    (ρ : M →* Pairing (A ⊕ A)) (hρ : Function.Injective ρ)
    (f : M →* N) (e : M) (he : e * e = e) (q : N) (hq : q * q = q) (hf : f e = q)
    (hmin : ∀ z : M, z * z = z → f z = q → Pairing.rank (ρ e) ≤ Pairing.rank (ρ z))
    (y : Corner e he) (hy : IsUnit (Corner.mapTo (he := he) (hq := hq) f hf y)) : IsUnit y := by sorry
