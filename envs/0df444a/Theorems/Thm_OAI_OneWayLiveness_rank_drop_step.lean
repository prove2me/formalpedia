-- Prove2me | Theorems.Thm_OAI_OneWayLiveness_rank_drop_step
-- name    : OAI.OneWayLiveness.rank_drop_step
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T04:24:16.537708+00:00
-- url     : https://prove2.me/theorems/fabd9e16-0768-45c2-9f3f-e7aaeaca3fa8
-- title:
--   A single new relation pair forces a rank drop of at least half the inductive rank loss
-- statement:
--   Let $\mathcal R_H$ denote the monoid of all binary relations on a set $H$, with product $RS=\{(x,z):\ (x,y)\in R \text{ and } (y,z)\in S \text{ for some } y\}$ (composition in diagrammatic order) and identity the diagonal $\Delta_H$. For $F\subseteq H$ write $\Delta_F=\{(z,z): z\in F\}$, and for $x,y\in H$ write $E_{x,y}=\Delta_H\cup\{(x,y)\}$ for the identity relation with one extra pair.
--
--   For a finite set $A$, let $\mathcal B_A$ be the Brauer monoid of $A$: an element is a perfect matching of the $2|A|$ ports $i_{\mathrm L},i_{\mathrm R}$ ($i\in A$), drawn with the left ports on one side and the right ports on the other; the product $\pi\sigma$ glues the right ports of $\pi$ to the left ports of $\sigma$, follows the resulting paths and discards closed loops, and the identity matches each $i_{\mathrm L}$ with $i_{\mathrm R}$. The rank $\operatorname{rk}\pi$ is the number of through strands, i.e. of $i\in A$ whose left port $i_{\mathrm L}$ is matched to some right port, and the support $\operatorname{supp}\pi$ is the set of $i\in A$ such that $i_{\mathrm L}$ is not matched to $i_{\mathrm R}$.
--
--   A homomorphism $\varphi\colon M\to\mathcal R_H$ has unit lifts if every unit of $\mathcal R_H$ (that is, the graph of a permutation of $H$) equals $\varphi(u)$ for some unit $u$ of $M$. For an idempotent $e$ of a monoid $M$, the corner $eMe=\{z\in M: ez=z=ze\}$ is a monoid with identity $e$. Put $\beta(h)=2^{\lfloor (h-2)/31\rfloor}$, where $h-2$ is read as $0$ when $h<2$; thus $\beta(h)=1$ for $h\le 32$. Say that the rank-loss property $\mathsf{RL}(h)$ holds if for all finite sets $H'$ and $A'$ with $|H'|=h$, every finite monoid $M'$, every injective homomorphism $\rho'\colon M'\to\mathcal B_{A'}$, every surjective homomorphism $\varphi'\colon M'\to\mathcal R_{H'}$ with unit lifts, and every idempotent $a\in M'$ with $\varphi'(a)=E_{x,y}$ for some $x\neq y$ in $H'$, one has $\beta(h)\le |A'|-\operatorname{rk}\rho'(a)$.
--
--   Now let $H$ and $A$ be finite sets, $M$ a finite monoid, $\rho\colon M\to\mathcal B_A$ an injective homomorphism and $\varphi\colon M\to\mathcal R_H$ a surjective homomorphism. Let $e\in M$ be idempotent, let $b$ be an idempotent of the corner $eMe$, and put $P=\varphi(e)$ and $N=\varphi(b)$. Let $F\subseteq H$ and assume:
--   1. $\Delta_F\,P\,\Delta_F=\Delta_F$, i.e. for $i,j\in F$ one has $(i,j)\in P$ if and only if $i=j$;
--   2. $PN=N$ and $NP=N$;
--   3. there are distinct $x,y\in F$ such that for all $i,j\in F$: $(i,j)\in N$ if and only if $i=j$ or $(i,j)=(x,y)$;
--   4. the rank-loss property $\mathsf{RL}(|F|)$ holds.
--
--   Then
--
--   $$\beta(|F|)\le 2\bigl(\operatorname{rk}\rho(e)-\operatorname{rk}\rho(b)\bigr).$$
--
--   Read $e$ as the current stage and $b$ as the next stage of a product being built: if the passage from $e$ to $b$ creates exactly one new pair on a set $F$ on which the current stage acts as the identity, then the diagram rank drops by at least $\beta(|F|)/2$. No unit-lift hypothesis is imposed on $\varphi$ and $e$ may be any idempotent, so the step can be applied at every stage of an inductive construction.
--
--   **Formalization Note** $b$ is an element of `Corner e he` and `b.val` is the underlying element of $M$; $\mathsf{RL}$ is `RankLossAt` (quantifying over types in `Type`) and $\beta$ is `rankLoss`. The difference of ranks is a natural-number subtraction, but no truncation occurs since $b=eb$ forces $\operatorname{rk}\rho(b)\le\operatorname{rk}\rho(e)$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Automata/RankLoss.lean#L18-L84

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

theorem OAI.OneWayLiveness.rank_drop_step {H A M : Type} [Fintype H] [Fintype A] [Monoid M] [Finite M]
    (ρ : M →* Pairing (A ⊕ A)) (hρ : Function.Injective ρ)
    (φ : M →* BRel H) (hφ : Function.Surjective φ)
    (e : M) (he : e * e = e) (b : Corner e he) (hb : b * b = b)
    (P N : BRel H) (heP : φ e = P) (hbN : φ b.val = N)
    (F : Set H) [Fintype F]
    (hF : BRel.restrictedId F * P * BRel.restrictedId F = BRel.restrictedId F)
    (hPN : P * N = N) (hNP : N * P = N)
    (x y : F) (hxy : x ≠ y)
    (hN : ∀ i j : F, N.holds i.val j.val ↔ (BRel.addEdge x y).holds i j)
    (hIH : RankLossAt (Fintype.card F)) :
    rankLoss (Fintype.card F) ≤ 2 * (Pairing.rank (ρ e) - Pairing.rank (ρ b.val)) := by sorry
