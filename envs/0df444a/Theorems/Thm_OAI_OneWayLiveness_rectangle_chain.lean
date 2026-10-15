-- Prove2me | Theorems.Thm_OAI_OneWayLiveness_rectangle_chain
-- name    : OAI.OneWayLiveness.rectangle_chain
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T04:24:56.987999+00:00
-- url     : https://prove2.me/theorems/43f81ec8-55c2-4152-a94c-8dc28fc12e5b
-- title:
--   Building a rectangle relation edge by edge accumulates rank loss inside a fixed support
-- statement:
--   Let $\mathcal R_H$ denote the monoid of all binary relations on a set $H$, with product $RS=\{(x,z):\ (x,y)\in R \text{ and } (y,z)\in S \text{ for some } y\}$ (composition in diagrammatic order) and identity the diagonal $\Delta_H$. For $F\subseteq H$ write $\Delta_F=\{(z,z): z\in F\}$, and for $x,y\in H$ write $E_{x,y}=\Delta_H\cup\{(x,y)\}$ for the identity relation with one extra pair.
--
--   For a finite set $A$, let $\mathcal B_A$ be the Brauer monoid of $A$: an element is a perfect matching of the $2|A|$ ports $i_{\mathrm L},i_{\mathrm R}$ ($i\in A$), drawn with the left ports on one side and the right ports on the other; the product $\pi\sigma$ glues the right ports of $\pi$ to the left ports of $\sigma$, follows the resulting paths and discards closed loops, and the identity matches each $i_{\mathrm L}$ with $i_{\mathrm R}$. The rank $\operatorname{rk}\pi$ is the number of through strands, i.e. of $i\in A$ whose left port $i_{\mathrm L}$ is matched to some right port, and the support $\operatorname{supp}\pi$ is the set of $i\in A$ such that $i_{\mathrm L}$ is not matched to $i_{\mathrm R}$.
--
--   A homomorphism $\varphi\colon M\to\mathcal R_H$ has unit lifts if every unit of $\mathcal R_H$ (that is, the graph of a permutation of $H$) equals $\varphi(u)$ for some unit $u$ of $M$. For an idempotent $e$ of a monoid $M$, the corner $eMe=\{z\in M: ez=z=ze\}$ is a monoid with identity $e$. Put $\beta(h)=2^{\lfloor (h-2)/31\rfloor}$, where $h-2$ is read as $0$ when $h<2$; thus $\beta(h)=1$ for $h\le 32$. Say that the rank-loss property $\mathsf{RL}(h)$ holds if for all finite sets $H'$ and $A'$ with $|H'|=h$, every finite monoid $M'$, every injective homomorphism $\rho'\colon M'\to\mathcal B_{A'}$, every surjective homomorphism $\varphi'\colon M'\to\mathcal R_{H'}$ with unit lifts, and every idempotent $a\in M'$ with $\varphi'(a)=E_{x,y}$ for some $x\neq y$ in $H'$, one has $\beta(h)\le |A'|-\operatorname{rk}\rho'(a)$.
--
--   A rectangle frame $(\ell,r,o)$ in a set $H$, indexed by sets $I$ and $J$, consists of injective maps $\ell\colon I\to H$ and $r\colon J\to H$ and a hub $o\in H$ such that $\ell(i)\neq r(j)$ for all $i\in I$, $j\in J$, and $o$ is neither of the form $\ell(i)$ nor of the form $r(j)$. For $E\subseteq I\times J$, the rectangle relation $R_E$ on $H$ relates $x$ to $y$ if and only if either $x=y\neq o$, or $(x,y)=(\ell(i),r(j))$ for some $(i,j)\in E$. So $R_E$ is the identity off the hub together with one edge from a left point to a right point for each pair in $E$.
--
--   Let $H,A,I,J$ be finite sets, $M$ a finite monoid, $\rho\colon M\to\mathcal B_A$ an injective and $\varphi\colon M\to\mathcal R_H$ a surjective homomorphism, and $(\ell,r,o)$ a rectangle frame in $H$ indexed by $I,J$. For an idempotent $e\in M$ let $L_e\subseteq A$ be the set of left through-strand endpoints of the idempotent diagram $\rho(e)$, so $|L_e|=\operatorname{rk}\rho(e)$. The diagram $\rho(e)$ factors through $L_e$ as $\rho(e)=\lambda_e\mu_e$, where $\lambda_e$ (left ports indexed by $A$, right ports by $L_e$) consists of the left caps of $\rho(e)$ together with the straight strands $i_{\mathrm L}$ to $i_{\mathrm R}$ for $i\in L_e$, and $\mu_e$ (left ports indexed by $L_e$, right ports by $A$) consists of the through strands and the right caps of $\rho(e)$; here a cap is a strand joining two ports on the same side. The reduction of $\rho$ at $e$ is the monoid homomorphism $\bar\rho_e\colon eMe\to\mathcal B_{L_e}$, $\bar\rho_e(z)=\mu_e\,\rho(z)\,\lambda_e$. For $(i,j)\in I\times J$ let
--
--   $$H_{ij}=H\setminus\bigl(\ell(I\setminus\{i\})\cup r(J\setminus\{j\})\cup\{o\}\bigr)$$
--
--   be the set retained when all frame points other than $\ell(i)$ and $r(j)$ are deleted. Assume:
--   1. $L\in\mathbb N$ satisfies $\beta(|H_{ij}|)=L$ for all $(i,j)$, and $\mathsf{RL}(|H_{ij}|)$ holds for all $(i,j)$;
--   2. $e\in M$ is idempotent with $\varphi(e)=R_\varnothing$;
--   3. $g\colon I\times J\to eMe$ satisfies $\varphi(g(p))=R_{\{p\}}$ for every $p\in I\times J$;
--   4. $K\subseteq L_e$ satisfies $\operatorname{supp}\bar\rho_e(g(p))\subseteq K$ for every $p$.
--
--   Then for every $E\subseteq I\times J$ there is an idempotent $b\in eMe$ with
--
--   $$\varphi(b)=R_E,\qquad \operatorname{supp}\bar\rho_e(b)\subseteq K,\qquad |E|\,L\le 2\bigl(\operatorname{rk}\rho(e)-\operatorname{rk}\rho(b)\bigr).$$
--
--   Each new rectangle edge thus costs at least $L/2$ in rank, while the support of the reduced diagram stays inside the fixed set $K$. With $|I|=|J|=16$ and $E=I\times J$ this produces the $256$-fold amplification in the exponential rank-loss theorem.
--
--   **Formalization Note** $\bar\rho_e$ is `Pairing.reduceHom ρ e he`, $L_e$ is the subtype `{i // i ∈ Pairing.lefts (ρ e)}`, $H_{ij}$ is `F.retained i j`, and $E$ ranges over finite sets (`Finset (I × J)`). The difference of ranks is a natural-number subtraction; no truncation occurs since $b=eb$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Automata/RankLoss.lean#L180-L266

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

theorem OAI.OneWayLiveness.rectangle_chain {H A M I J : Type} [Fintype H] [Fintype A]
    [Fintype I] [Fintype J] [Monoid M] [Finite M]
    (ρ : M →* Pairing (A ⊕ A)) (hρ : Function.Injective ρ)
    (φ : M →* BRel H) (hφ : Function.Surjective φ)
    (F : RectangleFrame H I J) (L : ℕ)
    (hL : ∀ i j, rankLoss (Fintype.card (F.retained i j)) = L)
    (hIH : ∀ i j, RankLossAt (Fintype.card (F.retained i j)))
    (e : M) (he : e * e = e) (heφ : φ e = F.base)
    (g : I × J → Corner e he)
    (hg : ∀ p, φ (g p).val = F.rel {p})
    (K : Finset {i // i ∈ Pairing.lefts (ρ e)})
    (hgK : ∀ p, Pairing.support (Pairing.reduceHom ρ e he (g p)) ⊆ K)
    (E : Finset (I × J)) :
    ∃ b : Corner e he, b * b = b ∧ φ b.val = F.rel (E : Set (I × J)) ∧
      Pairing.support (Pairing.reduceHom ρ e he b) ⊆ K ∧
      E.card * L ≤ 2 * (Pairing.rank (ρ e) - Pairing.rank (ρ b.val)) := by sorry
