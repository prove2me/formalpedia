-- Prove2me | Theorems.Thm_ObfImpossibility_PseudoOracle_inequality_8
-- name    : ObfImpossibility.PseudoOracle.inequality_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T10:28:25.655885+00:00
-- url     : https://prove2.me/theorems/2c06596d-b2cd-4967-9cbe-889d0709e365
-- title:
--   Inequality (8), p. A:44 — the query-free simulator $M$ built from $S_G$ and $G|_{[K]\setminus S_G}$ keeps the gap $>1/(2K^\delta)$
-- statement:
--   Let $K,L$ be natural numbers, $\delta\in\mathbb R$, $D$ a distinguisher, $G:[K]\to[L]$ injective and $S_G\subseteq[K]$. Define $M(y)$ to simulate $D(y)$, answering each oracle query $z\notin S_G$ with $G(z)$ and halting with output $0$ at a query $z\in S_G$. Assume
--
--   1. (Property 2 of Claim B.1.1) for every $x\in S_G$, $D^G(G(x))$ never queries its oracle at an element of $S_G$;
--   2. (Property 3, in the sign case at hand) $\Pr_{x\in S_G}[D^G(G(x))=1]-\Pr_{y\in L_G}[D^G(y)=1]>\frac1{2K^\delta}$, where $L_G=[L]\setminus G([K]\setminus S_G)$.
--
--   Then $M$ depends only on $S_G$ and the restriction $G|_{[K]\setminus S_G}$ (any injective $G'$ agreeing with $G$ off $S_G$ gives the same $M$), and
--   $$\Pr_{x\in S_G}\big[M(G(x))=1\big]-\Pr_{y\in L_G}\big[M(y)=1\big]>\frac{1}{2K^\delta}.\tag{8}$$
--
--   In the proof of Claim B.1.2 this lets the description of $G$ replace oracle access to $G$ on $S_G$: $M$ is computable from the part of $G$ already described, and it still separates $G(S_G)$ from $L_G$.
--
--   **Formalization Note** As in the paper, the absolute value of Property 3 is dropped and the case $\Pr_{x\in S_G}[\cdot]-\Pr_{y\in L_G}[\cdot]>\frac1{2K^\delta}$ is treated; the other case is symmetric (with $M$ outputting $1$ at a query in $S_G$) and is not stated. $M(y)$ is `(D y).runAvoid G S_G`.
-- source:
--   Barak et al., On the (Im)possibility of Obfuscating Programs, J. ACM 59(2) (2012), author's copy, p. A:44, Appendix B, proof of Claim B.1.2, inequality (8)

import Mathlib
import Definitions.Def_ObfImpossibility_PseudoOracle_Setting

namespace ObfImpossibility.PseudoOracle

/-- Inequality (8), p. A:44 (proof of Claim B.1.2). `M(y) := (D y).runAvoid G S_G`
simulates `D(y)`, answering a query `z ∉ S_G` with `G(z)` and halting with output `0` at a
query `z ∈ S_G`. Then `M` depends only on `S_G` and `G|_{[K] \ S_G}`, and if Property 2 of
Claim B.1.1 holds and `Pr_{x∈S_G}[D^G(G(x)) = 1] - Pr_{y∈L_G}[D^G(y) = 1] > 1/(2K^δ)`, then
`Pr_{x∈S_G}[M(G(x)) = 1] - Pr_{y∈L_G}[M(y) = 1] > 1/(2K^δ)`. -/
theorem inequality_8 (K L : ℕ) (δ : ℝ) (D : Fin L → QTree K L) (G : Fin K ↪ Fin L)
    (SG : Finset (Fin K))
    (hprop2 : ∀ x ∈ SG, (D (G x)).hits G SG = false)
    (hgap : 1 / (2 * (K : ℝ) ^ δ) <
      avg SG (fun x => (D (G x)).run G) - avg (LG G SG) (fun y => (D y).run G)) :
    (∀ G' : Fin K ↪ Fin L, (∀ z, z ∉ SG → G' z = G z) →
        ∀ y, (D y).runAvoid G' SG = (D y).runAvoid G SG) ∧
      1 / (2 * (K : ℝ) ^ δ) <
        avg SG (fun x => (D (G x)).runAvoid G SG) -
          avg (LG G SG) (fun y => (D y).runAvoid G SG) := by sorry

end ObfImpossibility.PseudoOracle
