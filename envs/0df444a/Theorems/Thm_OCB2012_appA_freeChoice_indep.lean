-- Prove2me | Theorems.Thm_OCB2012_appA_freeChoice_indep
-- name    : OCB2012.appA_freeChoice_indep
-- status  : Proved
-- author  : @Alien60
-- created : 2026-10-09T09:44:29.941263+00:00
-- url     : https://prove2.me/theorems/31ffc501-7054-4ee6-8748-99f3b034712f
-- title:
--   Appendix A: free choice implies the bits $a, b, b'$ are independent of the causal relation between $A_1$ and $B_1$
-- statement:
--   Let $p$ be a joint distribution of $(a,b,b',x,y,R)$ as in Appendix A, where $R$ is the causal relation between $A_1$ and $B_1$. Under assumption CS it takes exactly one of the values $A_1\preceq B_1$, $B_1\preceq A_1$ and $A_1\not\preceq\not\succeq B_1$. Assume the consequences of free choice (FC) that the paper invokes:
--
--   1. Bob's bits $b'$ and $b$ lie in the causal future of $B_1$. So each is independent of the event $A_1\preceq B_1$ and of the event $B_1\not\preceq A_1$:
--   $$p(b', A_1\preceq B_1) = p(b')\,p(A_1\preceq B_1),\qquad p(b', B_1\not\preceq A_1) = p(b')\,p(B_1\not\preceq A_1),$$
--   and the same for $b$.
--   2. Alice's bit $a$ lies in the causal future of $A_1$. So $a$ is independent of the event $B_1\preceq A_1$ and of the event $A_1\not\preceq B_1$.
--
--   Then each of $b'$, $b$ and $a$ is independent of the causal relation:
--
--   $$p(b', R) = p(b')\,p(R),\qquad p(b,R) = p(b)\,p(R),\qquad p(a,R) = p(a)\,p(R).$$
--
--   This is the step of Appendix A showing that 'the bits $a$, $b$, and $b'$ are independent of the causal relations between $A_1$ and $B_1$'. It uses that the three possibilities are mutually exclusive and exhaustive.
--
--   **Formalization Note.** Independence is stated in product form, $p(E\wedge F) = p(E)\,p(F)$, both in the hypotheses and in the conclusion. This avoids conditioning on zero-probability events.
-- source:
--   O. Oreshkov, F. Costa, C. Brukner, Quantum correlations with no causal order, Nat. Commun. 3, 1092 (2012), https://arxiv.org/abs/1105.4464v3, Appendix A, p. 7, first column ('Next, consider the three possibilities ... An analogous argument shows that a and b are also independent of the causal relation between A1 and B1')

import Mathlib
import Definitions.Def_OCB2012_appA

namespace OCB2012

open EventDist in
theorem appA_freeChoice_indep (P : EventDist) (hP : P.IsProb)
    (hb' : ∀ v,
      P.pr (fun _ _ b' _ _ R => decide (b' = v ∧ R = CausalRel.AB)) =
          P.pr (fun _ _ b' _ _ _ => decide (b' = v)) *
            P.pr (fun _ _ _ _ _ R => decide (R = CausalRel.AB)) ∧
      P.pr (fun _ _ b' _ _ R => decide (b' = v ∧ R ≠ CausalRel.BA)) =
          P.pr (fun _ _ b' _ _ _ => decide (b' = v)) *
            P.pr (fun _ _ _ _ _ R => decide (R ≠ CausalRel.BA)))
    (hb : ∀ v,
      P.pr (fun _ b _ _ _ R => decide (b = v ∧ R = CausalRel.AB)) =
          P.pr (fun _ b _ _ _ _ => decide (b = v)) *
            P.pr (fun _ _ _ _ _ R => decide (R = CausalRel.AB)) ∧
      P.pr (fun _ b _ _ _ R => decide (b = v ∧ R ≠ CausalRel.BA)) =
          P.pr (fun _ b _ _ _ _ => decide (b = v)) *
            P.pr (fun _ _ _ _ _ R => decide (R ≠ CausalRel.BA)))
    (ha : ∀ v,
      P.pr (fun a _ _ _ _ R => decide (a = v ∧ R = CausalRel.BA)) =
          P.pr (fun a _ _ _ _ _ => decide (a = v)) *
            P.pr (fun _ _ _ _ _ R => decide (R = CausalRel.BA)) ∧
      P.pr (fun a _ _ _ _ R => decide (a = v ∧ R ≠ CausalRel.AB)) =
          P.pr (fun a _ _ _ _ _ => decide (a = v)) *
            P.pr (fun _ _ _ _ _ R => decide (R ≠ CausalRel.AB))) :
    ∀ v R₀,
      P.pr (fun _ _ b' _ _ R => decide (b' = v ∧ R = R₀)) =
          P.pr (fun _ _ b' _ _ _ => decide (b' = v)) * P.pr (fun _ _ _ _ _ R => decide (R = R₀)) ∧
      P.pr (fun _ b _ _ _ R => decide (b = v ∧ R = R₀)) =
          P.pr (fun _ b _ _ _ _ => decide (b = v)) * P.pr (fun _ _ _ _ _ R => decide (R = R₀)) ∧
      P.pr (fun a _ _ _ _ R => decide (a = v ∧ R = R₀)) =
          P.pr (fun a _ _ _ _ _ => decide (a = v)) * P.pr (fun _ _ _ _ _ R => decide (R = R₀)) := by sorry

end OCB2012
