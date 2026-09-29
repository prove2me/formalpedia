-- Prove2me | Theorems.Thm_MoreauProx_Decomposition_moreau_decomposition
-- name    : MoreauProx.Decomposition.moreau_decomposition
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T16:13:04.103434+00:00
-- url     : https://prove2.me/theorems/db72349f-dc3b-4f9d-ad8b-55a897d359bb
-- title:
--   Proposition 4.a — Moreau's decomposition: z = x + y with x, y conjugate iff x = prox_f z and y = prox_g z
-- statement:
--   Let $H$ be a real Hilbert space with inner product $(x\mid y)$, let $f \in \Gamma_0(H)$, and let $g = f^{*}$ be its dual function, $g(y) = \sup_{u\in H}[(u\mid y) - f(u)]$. For $z \in H$ write $\mathrm{prox}_f z$ for the unique minimizer of $u \mapsto \tfrac12\|u - z\|^2 + f(u)$, and similarly $\mathrm{prox}_g z$. Then for all $x, y, z \in H$ the following two properties are equivalent:
--
--   $$ \text{(I)}\quad z = x + y \quad\text{and}\quad f(x) + g(y) = (x \mid y); $$
--   $$ \text{(II)}\quad x = \mathrm{prox}_f z \quad\text{and}\quad y = \mathrm{prox}_g z. $$
--
--   In particular every $z \in H$ decomposes uniquely as $z = \mathrm{prox}_f z + \mathrm{prox}_g z$ into two points conjugate with respect to $f$ and its dual. For $f$ the indicator of a closed subspace this is the orthogonal decomposition; for the indicator of a closed convex cone it is the decomposition into projections onto the cone and its polar cone.
--
--   **Formalization Note** The paper assumes $f, g \in \Gamma_0(H)$ "dual to each other". Here only $f \in \Gamma_0(H)$ and $g = f^{*}$ are assumed; $g \in \Gamma_0(H)$ and $f = g^{*}$ then follow (§2.b), so this statement is equivalent to the paper's and not weaker. "$x = \mathrm{prox}_f z$" is stated as "$x$ minimizes $u \mapsto \tfrac12\|u-z\|^2 + f(u)$" (`IsProx`), which is equivalent because that minimizer exists and is unique (Proposition 3.a). The identity in (I) is an equation in `EReal`.
-- source:
--   Moreau, Proximité et dualité dans un espace hilbertien, Bull. Soc. Math. France 93 (1965), p. 280, Proposition 4.a

import Mathlib
import Definitions.Def_MoreauProx_Decomposition_ConvexDuality

namespace MoreauProx.Decomposition

open scoped InnerProductSpace

/-- Moreau 1965, Proposition 4.a, p. 280: let `f, g ∈ Γ₀(H)` be dual to each other and
`x, y, z ∈ H`. Then (I) `z = x + y` and `f(x) + g(y) = (x | y)` holds iff
(II) `x = prox_f z` and `y = prox_g z`. Stated with `f ∈ Γ₀(H)` and `g` the dual of `f`
(then `g ∈ Γ₀(H)` and `f` is the dual of `g` by §2.b). -/
theorem moreau_decomposition {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (f g : H → EReal) (hf : GammaZero f) (hg : g = conj f) (x y z : H) :
    (z = x + y ∧ f x + g y = ((⟪x, y⟫_ℝ : ℝ) : EReal)) ↔ (IsProx f z x ∧ IsProx g z y) := by sorry

end MoreauProx.Decomposition
