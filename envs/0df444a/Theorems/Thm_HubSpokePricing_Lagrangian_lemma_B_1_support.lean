-- Prove2me | Theorems.Thm_HubSpokePricing_Lagrangian_lemma_B_1_support
-- name    : HubSpokePricing.Lagrangian.lemma_B_1_support
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-10-30T19:16:00.062879+00:00
-- url     : https://prove2.me/theorems/3d51a433-6722-4caf-8f55-13a8cd5c8810
-- title:
--   Lemma B.1 (items 1, 3), p. 64 — the optimal spoke support is the irreducible interval [0 : H_i]
-- statement:
--   Let $N$ be a hub-and-spoke network satisfying the standing assumptions (Assumption 2.1). Fix a dual price $\lambda\ge0$ and a spoke $i$, and let $\big(p_i(x),\,d_i(x,i,0),\,d_i(x,0,i)\big)_{x\in[0:m]}$ be an optimal solution of the spoke problem (6). Write
--   $$I_i=\{x\in[0:m]:p_i(x)>0\},\qquad H_i=\max I_i .$$
--   Then:
--
--   1. **The support is an interval:** $I_i=[0:H_i]$, i.e. $p_i(x)>0$ if and only if $x\le H_i$.
--   2. **The support is irreducible:** for every $x\in[0:m-1]$ with $x+1\in I_i$, both the control that moves the spoke up from $x$ and the control that moves it down from $x+1$ are positive,
--   $$d_i(x,0,i)>0\qquad\text{and}\qquad d_i(x+1,i,0)>0 .$$
--   So the birth–death chain of the spoke under these controls communicates between all levels of $[0:H_i]$.
--
--   These are items 1 and 3 of Lemma B.1: $I_i$ is the single positive recurrent class, and $I_i=[0:H_i]$. They are proved through Propositions B.2–B.7. Irreducibility (Proposition B.6) uses the complementary slackness of (6) and the fact that the revenue maximizers $\arg\max_{[0,1]}r_{i0}$ and $\arg\max_{[0,1]}r_{0i}$ are positive. Together with the monotonicity of the controls (Proposition 3.3), these facts give the log-concavity of $p_i$ (Proposition B.9).
--
--   **Formalization Note.** $H_i$ is `SpokeSol.top`. Item 2 is stated in the form the proof of Proposition B.9 uses: positivity of `s.dIn x.castSucc` and `s.dOut x.succ` whenever `0 < s.p x.succ`. Given the flow-balance constraint of (6), this is equivalent to $I_i$ being one communicating class.
-- source:
--   Balseiro, Brown & Chen, Dynamic Pricing of Relocating Resources in Large Networks, SSRN 3313737 (version of May 23, 2020), https://ssrn.com/abstract=3313737, Appendix B, Lemma B.1 items 1 and 3, p. 64, proved via Propositions B.2–B.7, pp. 64–65 (irreducibility: Proposition B.6)

import Mathlib
import Definitions.Def_HubSpokePricing_Lagrangian_Model

namespace HubSpokePricing.Lagrangian

/-- Lemma B.1, items 1 and 3 (p. 64; Propositions B.2–B.7, pp. 64–65): for an optimal solution of
the spoke problem (6), the support `I_i = {x : p_i(x) > 0}` is the interval `[0 : H_i]`, and it is a
single irreducible class of the birth–death chain driven by the controls: inside `I_i` both the
up-move control `d_i(x, 0, i)` and the down-move control `d_i(x + 1, i, 0)` are positive. -/
theorem lemma_B_1_support (N : Network) (hN : N.Standing) (lam : ℝ) (hlam : 0 ≤ lam)
    (i : Fin N.n) (s : SpokeSol N.m) (hs : SpokeOptimal N lam i s) :
    (∀ x : Fin (N.m + 1), 0 < s.p x ↔ (x : ℕ) ≤ s.top) ∧
      ∀ x : Fin N.m, 0 < s.p x.succ → 0 < s.dIn x.castSucc ∧ 0 < s.dOut x.succ := by sorry

end HubSpokePricing.Lagrangian
