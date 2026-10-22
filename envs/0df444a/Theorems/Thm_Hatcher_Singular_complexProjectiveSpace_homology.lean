-- Prove2me | Theorems.Thm_Hatcher_Singular_complexProjectiveSpace_homology
-- name    : Hatcher.Singular.complexProjectiveSpace_homology
-- status  : Proved
-- author  : @Idealson
-- created : 2026-10-21T08:27:56.743467+00:00
-- url     : https://prove2.me/theorems/77b4263e-3846-4da4-bc2e-a3711327b514
-- title:
--   Homology of $\mathbb CP^n$: $R$ in even degrees $0,2,\dots,2n$ and $0$ otherwise
-- statement:
--   Let $R$ be a ring, $n\ge 0$, and let $\mathbb CP^n$ be complex projective $n$-space, the quotient of $\mathbb C^{n+1}\setminus\{0\}$ by the scalar action of $\mathbb C^\times$, with the quotient topology. Then:
--
--   1. $H_k(\mathbb CP^n;R)=0$ whenever $k$ is odd or $k>2n$;
--   2. $H_{2i}(\mathbb CP^n;R)\cong R$ for every $0\le i\le n$.
--
--   In other words
--   $$H_k(\mathbb CP^n;R)\cong\begin{cases}R,&k=0,2,4,\dots,2n,\\0,&\text{otherwise.}\end{cases}$$
--
--   This is the basic example of a space whose homology is concentrated in even degrees; with $R=\mathbb Q$ it gives the Betti numbers of $\mathbb P^n(\mathbb C)$, which appear in the Weil conjectures for projective space.
--
--   **Formalization Note** $\mathbb CP^n$ is `Hatcher.CP n` from `Hatcher_ComplexProjectiveSpace`. Vanishing is `IsZero` in the category of $R$-modules; the isomorphisms are isomorphisms of $R$-modules.
-- source:
--   A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002 (online edition: https://pi.math.cornell.edu/~hatcher/AT/AT.pdf), §2.2, “Cellular Homology”: Theorem 2.35 (p. 139) and application (iii) on p. 140, which gives $H_i(\mathbb CP^n)\cong\mathbb Z$ for $i=0,2,\dots,2n$ and $0$ otherwise; arbitrary coefficients as in §2.2 (p. 153); $\mathbb CP^n$ as in Example 0.6 (p. 6). Lean: original formalization for this project (Lean v4.33.1, Mathlib 0df444a), file `Bridge/Singular/ComplexProjective.lean`.

import Mathlib
import Definitions.Def_Hatcher_SingularHomology
import Definitions.Def_Hatcher_ComplexProjectiveSpace

open CategoryTheory Limits

theorem Hatcher.Singular.complexProjectiveSpace_homology (R : Type) [Ring R] (n : ℕ) :
    (∀ k : ℕ, (Odd k ∨ 2 * n < k) → IsZero (H R k (CP n))) ∧
    (∀ i : ℕ, i ≤ n → Nonempty (H R (2 * i) (CP n) ≅ ModuleCat.of R R)) := by sorry
