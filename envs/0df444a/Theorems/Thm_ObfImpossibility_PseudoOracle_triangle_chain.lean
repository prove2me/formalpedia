-- Prove2me | Theorems.Thm_ObfImpossibility_PseudoOracle_triangle_chain
-- name    : ObfImpossibility.PseudoOracle.triangle_chain
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T10:28:14.101025+00:00
-- url     : https://prove2.me/theorems/5a731d30-84e4-41f5-a8fb-b6590fa3eff0
-- title:
--   Proof of Claim B.1.1, p. A:44 — the triangle-inequality chain giving Property 3, $|\Pr_{S_G}-\Pr_{L_G}|>1/(2K^\delta)$
-- statement:
--   For every $0<\delta\le1/100$ there is $K_0$ such that the following holds for all $K\ge K_0$ and $L\ge K^2$. Let $D$ be a distinguisher, $G:[K]\to[L]$ injective, and $S_G\subseteq S\subseteq[K]$ with $|S_G|\ge(1-\gamma)|S|$, where $\gamma=K^{-3\delta}$. Write $f(x)=D^G(G(x))$, $g(y)=D^G(y)$ and $L_G=[L]\setminus G([K]\setminus S_G)$. Assume that $G$ violates inequality (7),
--   $$\Big|\Pr_{x\in[K]}[f(x)=1]-\Pr_{y\in[L]}[g(y)=1]\Big|>\frac1{K^\delta},$$
--   and that $S$ satisfies the Chernoff-like bound $\big|\Pr_{x\in S}[f(x)=1]-\Pr_{x\in[K]}[f(x)=1]\big|\le\frac1{4K^\delta}$. Then
--   $$\begin{aligned}\Big|\Pr_{x\in S_G}[f(x)=1]-\Pr_{y\in L_G}[g(y)=1]\Big| \ \ge\ & \Big|\Pr_{x\in[K]}[f(x)=1]-\Pr_{y\in[L]}[g(y)=1]\Big| -\Big|\Pr_{x\in S_G}[f(x)=1]-\Pr_{x\in S}[f(x)=1]\Big|\\ &-\Big|\Pr_{x\in S}[f(x)=1]-\Pr_{x\in[K]}[f(x)=1]\Big|-\Big|\Pr_{y\in[L]}[g(y)=1]-\Pr_{y\in L_G}[g(y)=1]\Big|\end{aligned}$$
--   and
--   $$\Big|\Pr_{x\in S_G}[f(x)=1]-\Pr_{y\in L_G}[g(y)=1]\Big|>\frac{1}{2K^\delta}.$$
--
--   This is the computation that turns a violation of (7) on all of $[K]$ and $[L]$ into a violation on the smaller sets $S_G$ and $L_G$, i.e. Property 3 of Claim B.1.1. The paper bounds the three subtracted gaps by $\gamma$, $\frac1{4K^\delta}$ and $K/L$ and uses that $K^{-\delta}-\gamma-\frac1{4K^\delta}-\frac KL>\frac1{2K^\delta}$ for large $K$; its "$x\in[S]$" in the second gap is a misprint for $x\in S$.
--
--   **Formalization Note** Both conclusions are stated; the first is a pure triangle inequality. Property (1) is read as $|S_G|\ge(1-\gamma)|S|$.
-- source:
--   Barak et al., On the (Im)possibility of Obfuscating Programs, J. ACM 59(2) (2012), author's copy, p. A:44, Appendix B, end of the proof of Claim B.1.1 (display; x∈[S] read as x∈S)

import Mathlib
import Definitions.Def_ObfImpossibility_PseudoOracle_Setting

namespace ObfImpossibility.PseudoOracle

/-- The chain of inequalities closing the proof of Claim B.1.1, p. A:44: if `G` violates
(7), `S_G ⊆ S` with `|S_G| ≥ (1-γ)|S|`, `γ = K^{-3δ}`, and `S` satisfies the Chernoff-like
bound, then the four gaps satisfy the triangle inequality, and Property 3 holds:
`|Pr_{x∈S_G}[D^G(G(x)) = 1] - Pr_{y∈L_G}[D^G(y) = 1]| > 1/(2K^δ)`. -/
theorem triangle_chain :
    ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 100 → ∃ K₀ : ℕ, ∀ K L : ℕ, K₀ ≤ K → K ^ 2 ≤ L →
      ∀ (D : Fin L → QTree K L) (G : Fin K ↪ Fin L) (S SG : Finset (Fin K)),
        SG ⊆ S →
        (1 - (K : ℝ) ^ (-(3 * δ))) * (S.card : ℝ) ≤ (SG.card : ℝ) →
        1 / (K : ℝ) ^ δ < |prX D G - prY D G| →
        |avg S (fun x => (D (G x)).run G) - prX D G| ≤ 1 / (4 * (K : ℝ) ^ δ) →
        |prX D G - prY D G|
            - |avg SG (fun x => (D (G x)).run G) - avg S (fun x => (D (G x)).run G)|
            - |avg S (fun x => (D (G x)).run G) - prX D G|
            - |prY D G - avg (LG G SG) (fun y => (D y).run G)|
          ≤ |avg SG (fun x => (D (G x)).run G) - avg (LG G SG) (fun y => (D y).run G)| ∧
        1 / (2 * (K : ℝ) ^ δ) <
          |avg SG (fun x => (D (G x)).run G) - avg (LG G SG) (fun y => (D y).run G)| := by sorry

end ObfImpossibility.PseudoOracle
