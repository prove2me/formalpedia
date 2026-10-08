-- Prove2me | Theorems.Thm_JeroslowMLP_Value_lemma_4_1
-- name    : JeroslowMLP.Value.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T10:02:09.124987+00:00
-- url     : https://prove2.me/theorems/782d4cfe-9883-40cf-95b4-e9b5fefe83b6
-- title:
--   Lemma 4.1, p. 156 — atoms within δ of a binary assignment force |x(G) − x⁰(G)| < γ when δL ≤ γ
-- statement:
--   Let $G$ be a propositional formula of length $L$ and let $\delta,\gamma>0$ with $\delta L\le\gamma$. Let $x^0$ be a truth assignment of the atoms, and write $x^0(A)$, $x^0(G)\in\{0,1\}$ for the binary values of an atom and of $G$ under it. Suppose real values $x(A)$ of the atoms satisfy
--   $$|x(A)-x^0(A)|<\delta\quad\text{for every atom } A \text{ occurring in } G, \qquad (4.9)$$
--   and that the node values $x(\cdot)$ solve the system (3.1) of $G$ (with each node value in $[0,1]$). Then
--   $$|x(G)-x^0(G)|<\gamma. \qquad (4.10)$$
--
--   The lemma is a robustness property of $L_G$: near-binary inputs produce an output near the correct truth value. It is what allows player 1 in $J'(F)$ to be forced to binary choices.
--
--   **Formalization Note** The atom type is arbitrary, the length is the one of the `Formula` definition (atom $1$, each connective $+1$), and hypothesis (4.9) is required only on the atoms occurring in $G$.
-- source:
--   Jeroslow, The polynomial hierarchy and a simple model for competitive analysis, Math. Programming 32 (1985), p. 156, Lemma 4.1, (4.9)–(4.10)

import Mathlib
import Definitions.Def_JeroslowMLP_Value_Formula

namespace JeroslowMLP.Value

theorem lemma_4_1 {α : Type} (G : Formula α) (δ γ : ℝ) (hδ : 0 < δ) (hγ : 0 < γ)
    (hδγ : δ * (G.length : ℝ) ≤ γ) (x₀ : α → Bool) (xa : α → ℝ) (xn : G.Node → ℝ)
    (h49 : ∀ a ∈ G.atoms, |xa a - (if x₀ a then 1 else 0)| < δ)
    (hsys : G.LSys xa xn) :
    |G.nodeVal xa xn - (if G.eval x₀ then 1 else 0)| < γ := by sorry

end JeroslowMLP.Value
