-- Prove2me | Theorems.Thm_LeblSCV_Varieties_singular_set_of_hypervariety
-- name    : LeblSCV.Varieties.singular_set_of_hypervariety
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T10:16:53.859722+00:00
-- url     : https://prove2.me/theorems/7340ee71-0893-4262-ab0d-0ab20b97d9d3
-- title:
--   Theorem 6.6.5 — the singular set of a hypervariety is a subvariety of dimension at most n − 2
-- statement:
--   Let $U \subset \mathbb{C}^n$ be open and let $X \subset U$ be a subvariety of pure codimension $1$ (a hypervariety): at every regular point $q$ of $X$, $\dim_q X = n - 1$. Let $X_{\mathrm{sing}} = X \setminus X_{\mathrm{reg}}$ be its set of singular points. Then $X_{\mathrm{sing}}$ is a subvariety of $U$ and
--   $$\dim X_{\mathrm{sing}} \le n - 2 .$$
--
--   This is the codimension-1 case of the general fact (stated without proof in the book as Theorem 6.5.11) that the singular set of any subvariety is a lower-dimensional subvariety. In particular, a hypervariety of $\mathbb{C}^1$ has no singular points, and the singular set of a hypervariety of $\mathbb{C}^2$ (a complex curve) has dimension at most $0$.
--
--   **Formalization Note.** $\dim X_{\mathrm{sing}} \le n-2$ is stated as "every regular point $q$ of $X_{\mathrm{sing}}$ has $\dim_q X_{\mathrm{sing}} \le n - 2$" with $n - 2$ computed in `ℤ`: for $n = 1$ it forces $X_{\mathrm{sing}}$ to have no regular points (hence, being a subvariety, to be empty), and when $X_{\mathrm{sing}} = \emptyset$ it holds vacuously, where the book's $\max$ over an empty set is undefined. Holomorphic is `DifferentiableOn ℂ` on open sets, and $\mathbb{C}^n$ is `Fin n → ℂ`.
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), p. 191, Theorem 6.6.5

import Mathlib
import Definitions.Def_LeblSCV_Varieties_IsSubvariety
import Definitions.Def_LeblSCV_Varieties_IsPureCodim
import Definitions.Def_LeblSCV_Varieties_singularPoints
import Definitions.Def_LeblSCV_Varieties_IsDimLE

namespace LeblSCV.Varieties

/-- Lebl, Theorem 6.6.5: let `U ⊆ ℂⁿ` be open and `X ⊆ U` a subvariety of pure codimension 1
(a hypervariety). Then `X_sing` is a subvariety of `U` of dimension at most `n - 2`
(every regular point of `X_sing` has dimension `≤ n - 2`, computed in `ℤ`; for `n = 1` this forces
`X_sing` to have no regular points). -/
theorem singular_set_of_hypervariety {n : ℕ} {U X : Set (Fin n → ℂ)}
    (hX : IsSubvariety U X) (hpure : IsPureCodim X 1) :
    IsSubvariety U (singularPoints X) ∧ IsDimLE (singularPoints X) ((n : ℤ) - 2) := by sorry

end LeblSCV.Varieties
