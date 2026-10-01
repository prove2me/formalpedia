-- Prove2me | Theorems.Thm_FoundationsML_Stability_kernel_regularization_stability
-- name    : FoundationsML.Stability.kernel_regularization_stability
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-20T04:24:51.660793+00:00
-- url     : https://prove2.me/theorems/e983014c-e918-4a8e-af4e-99945621e41a
-- title:
--   Proposition 14.4 — stability of kernel-based regularization algorithms
-- statement:
--   **Statement (Proposition 14.4, p. 338, PDF p. 355).** Let $K$ be a PDS kernel with
--   $K(x,x)\le r^2$ for all $x\in X$, and $L$ a convex, $\sigma$-admissible loss function. Then
--   the kernel-based regularization algorithm defined by minimizing $F_S(h) = \hat R_S(h) +
--   \lambda\|h\|_K^2$ is $\beta$-stable with $\beta \le \sigma^2r^2/(m\lambda)$.
--
--   This is the chapter's general upper bound on the stability coefficient for the whole family
--   of kernel-based regularization algorithms (KRR, SVR, SVMs all instantiate it), feeding the
--   specific $\beta$ into Theorem 14.2's generic stability bound.
--
--   **Formalization Note.** Stated pairwise: for any samples $S$, $S'$ differing by one point
--   and any minimizers $h$ of $F_S$, $h'$ of $F_{S'}$, the pointwise loss difference is bounded
--   by $\sigma^2r^2/(m\lambda)$ — the content of Definition 14.1 instantiated at this specific
--   pair, avoiding the need to fix a canonical choice function when minimizers are not unique.
--   An explicit convexity hypothesis on $L(\cdot,y)$ (for every $y$) is carried, matching the
--   book's own "let $L$ be a convex and $\sigma$-admissible loss function": the book's proof
--   (PDF pp. 354-356) rests on the non-negativity of the generalized Bregman divergence of
--   $F_S$, which holds only because $F_S$ (hence $L$) is convex.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 338, Proposition 14.4 (PDF p. 355)

import Mathlib
import Definitions.Def_FoundationsML_Stability_EmpiricalError
import Definitions.Def_FoundationsML_Stability_SigmaAdmissible
import Definitions.Def_FoundationsML_Stability_IsRKHSOf
import Definitions.Def_FoundationsML_Stability_IsMinimizer

namespace FoundationsML.Stability

/-- Proposition 14.4 (Mohri, Rostamizadeh & Talwalkar, *Foundations of Machine Learning*, 2nd
ed., MIT Press 2018, p. 338, PDF p. 355). Let `K` be a PDS kernel with `K(x,x) ≤ r²` for all
`x ∈ X`, and `L` a convex, σ-admissible loss function. Then the kernel-based regularization
algorithm defined by minimizing `F_S(h) = R̂_S(h) + λ‖h‖²_K` is `β`-stable with `β ≤ σ²r²/(mλ)`.

**Formalization Note.** Stated pairwise: for any samples `S`, `S'` differing by one point and
any minimizers `h` of `F_S`, `h'` of `F_{S'}`, the pointwise loss difference is bounded by
`σ²r²/(mλ)` — the content of Definition 14.1 instantiated at this specific pair, avoiding the
need to fix a canonical choice function when minimizers are not unique (the book's own proof
picks an arbitrary minimizer of each).

**Revision (2026-09-19).** Added `hLconv : ∀ y : Y, ConvexOn ℝ Set.univ (fun y' : ℝ => L y' y)`
(convexity of `L(·,y)` in its first argument, for every `y`), matching the book's own hypothesis
"let `L` be a convex and σ-admissible loss function." This is not decoration: the book's own
proof (PDF pp. 354-356) is built on the non-negativity of the generalized Bregman divergence of
`F_S`, which holds only because `F_S` (hence `L`) is convex — for a non-convex σ-admissible `L`,
subgradients need not exist and the divergence need not be non-negative, so the derivation does
not go through, and the book chose not to claim the bound holds without convexity. -/
theorem kernel_regularization_stability
    {X Y H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (K : X → X → ℝ) (Φ : X → H) (ev : H → X → ℝ) (hRKHS : IsRKHSOf K Φ ev)
    (r : ℝ) (hr : 0 ≤ r) (hK : ∀ x : X, K x x ≤ r ^ 2)
    (L : ℝ → Y → ℝ) (σ : ℝ) (hσ : 0 ≤ σ) (hAdm : SigmaAdmissible ev L σ)
    (hLconv : ∀ y : Y, ConvexOn ℝ Set.univ (fun y' : ℝ => L y' y))
    {m : ℕ} (hm : 0 < m) (lam : ℝ) (hlam : 0 < lam)
    (S S' : Fin m → X × Y) (hSS' : ∃ i : Fin m, ∀ j : Fin m, j ≠ i → S j = S' j)
    (h h' : H)
    (hmin : IsMinimizer (fun g : H => EmpiricalError L S (ev g) + lam * ‖g‖ ^ 2) h)
    (hmin' : IsMinimizer (fun g : H => EmpiricalError L S' (ev g) + lam * ‖g‖ ^ 2) h') :
    ∀ z : X × Y, |Loss L (ev h) z - Loss L (ev h') z| ≤ σ ^ 2 * r ^ 2 / (m * lam) := by sorry

end FoundationsML.Stability
