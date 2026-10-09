-- Prove2me | Theorems.Thm_OCB2012_appA_causal_inequality
-- name    : OCB2012.appA_causal_inequality
-- status  : Proved
-- author  : @Alien60
-- created : 2026-10-09T09:44:29.415018+00:00
-- url     : https://prove2.me/theorems/c146c6f7-65b0-4d40-b1b7-12eff2a821db
-- title:
--   Appendix A, Eqs. (9)–(10): free choice and closed laboratories imply $p_{succ}\le 3/4$
-- statement:
--   Let $p(a,b,b',x,y,R)$ be a joint distribution of Alice's bit $a$, Bob's bits $b,b'$, the guesses $x, y$, and the causal relation $R\in\{A_1\preceq B_1,\ B_1\preceq A_1,\ A_1\not\preceq\not\succeq B_1\}$ between the events $A_1$ and $B_1$. Assume:
--
--   1. **(FC, as used in App. A)** the bits $a, b, b'$ are uniformly distributed, mutually independent, and jointly independent of $R$:
--   $$p(a,b,b',R) = \tfrac18\,p(R);$$
--   2. **(CL for Alice)** whenever $B_1\not\preceq A_1$ (that is, $R$ is $A_1\preceq B_1$ or incomparable), Alice's guess $x$ is uncorrelated with $b$, conditionally on $b'$ and $R$:
--   $$p(x,b,b',R)\,p(b',R) = p(x,b',R)\,p(b,b',R);$$
--   3. **(CL for Bob)** whenever $A_1\not\preceq B_1$, Bob's guess $y$ is uncorrelated with $a$, conditionally on $b'$ and $R$.
--
--   Then
--
--   $$p_{succ} = \tfrac12\,p(x=b\mid b'=0) + \tfrac12\,p(y=a\mid b'=1)\;\le\;\tfrac34 .$$
--
--   This is the paper's formal derivation of the causal inequality (2) from the assumptions CS, FC and CL (Eqs. (9)–(10) and the case analysis that follows). It holds without any reference to quantum mechanics.
--
--   **Formalization Note.** The independence of $a, b, b'$ from each other and from $R$ is derived informally in the paper from FC. Here it is taken as hypothesis 1. Its derivation for the causal relation is the separate milestone `OCB2012.appA_freeChoice_indep`. Conditional independences are stated in product form, which avoids dividing by zero-probability events.
-- source:
--   O. Oreshkov, F. Costa, C. Brukner, Quantum correlations with no causal order, Nat. Commun. 3, 1092 (2012), https://arxiv.org/abs/1105.4464v3, Appendix A, pp. 6-7, Eqs. (9)-(10) and the concluding case analysis

import Mathlib
import Definitions.Def_OCB2012_appA

namespace OCB2012

open EventDist in
theorem appA_causal_inequality (P : EventDist) (hP : P.IsProb)
    (hFC : ∀ a₀ b₀ b'₀ R₀,
      P.pr (fun a b b' _ _ R => decide (a = a₀ ∧ b = b₀ ∧ b' = b'₀ ∧ R = R₀)) =
        (1 / 8 : ℝ) * P.pr (fun _ _ _ _ _ R => decide (R = R₀)))
    (hCLx : ∀ R₀, R₀ ≠ CausalRel.BA → ∀ b'₀ x₀ b₀,
      P.pr (fun _ b b' x _ R => decide (x = x₀ ∧ b = b₀ ∧ b' = b'₀ ∧ R = R₀)) *
          P.pr (fun _ _ b' _ _ R => decide (b' = b'₀ ∧ R = R₀)) =
        P.pr (fun _ _ b' x _ R => decide (x = x₀ ∧ b' = b'₀ ∧ R = R₀)) *
          P.pr (fun _ b b' _ _ R => decide (b = b₀ ∧ b' = b'₀ ∧ R = R₀)))
    (hCLy : ∀ R₀, R₀ ≠ CausalRel.AB → ∀ b'₀ y₀ a₀,
      P.pr (fun a _ b' _ y R => decide (y = y₀ ∧ a = a₀ ∧ b' = b'₀ ∧ R = R₀)) *
          P.pr (fun _ _ b' _ _ R => decide (b' = b'₀ ∧ R = R₀)) =
        P.pr (fun _ _ b' _ y R => decide (y = y₀ ∧ b' = b'₀ ∧ R = R₀)) *
          P.pr (fun a _ b' _ _ R => decide (a = a₀ ∧ b' = b'₀ ∧ R = R₀))) :
    P.pSucc ≤ 3 / 4 := by sorry

end OCB2012
