-- Prove2me | Theorems.Thm_MoreauProx_Characterization_moreau_decomposition
-- name    : MoreauProx.Characterization.moreau_decomposition
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T16:18:36.356161+00:00
-- url     : https://prove2.me/theorems/8d6be128-11c6-4cdd-b687-bcae5b618cad
-- title:
--   Proposition 4.a — Moreau's decomposition: z = x + y with x, y conjugate iff x = prox_f z, y = prox_g z
-- statement:
--   Let $H$ be a real Hilbert space, let $f \in \Gamma_0(H)$, and let $g$ be the dual function of $f$. For all $x, y, z \in H$ the following are equivalent:
--
--   1. $z = x + y$ and $f(x) + g(y) = (x \mid y)$;
--   2. $x = \operatorname{prox}_f z$ and $y = \operatorname{prox}_g z$, i.e. $x$ minimizes $u \mapsto \tfrac12\|u - z\|^2 + f(u)$ and $y$ minimizes $u \mapsto \tfrac12\|u - z\|^2 + g(u)$.
--
--   In short, every $z \in H$ splits uniquely as $z = \operatorname{prox}_f z + \operatorname{prox}_g z$, and the two parts are conjugate points for the pair $(f, g)$. This is the key proposition of the paper: the results of Sections 5–10 are derived from it.
--
--   **Formalization Note** The paper assumes $f, g \in \Gamma_0(H)$ dual to each other; we assume $f \in \Gamma_0(H)$ and $g = f^*$, which the paper's hypothesis implies, so the statement is at least as strong. "$x = \operatorname{prox}_f z$" is stated as "$x$ minimizes the proximal objective", which is equivalent because the minimizer is unique (Proposition 3.a).
-- source:
--   Moreau, Proximité et dualité dans un espace hilbertien, Bull. Soc. Math. France 93 (1965), p. 280, Proposition 4.a

import Mathlib
import Definitions.Def_MoreauProx_Characterization_Prox
open scoped InnerProductSpace

namespace MoreauProx.Characterization

theorem moreau_decomposition {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f g : H → EReal) (hf : GammaZero f) (hg : g = conj f) (x y z : H) :
    (z = x + y ∧ f x + g y = ((⟪x, y⟫_ℝ : ℝ) : EReal)) ↔ (IsProx f z x ∧ IsProx g z y) := by sorry

end MoreauProx.Characterization
