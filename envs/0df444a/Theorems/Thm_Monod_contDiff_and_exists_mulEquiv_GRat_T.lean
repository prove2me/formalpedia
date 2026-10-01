-- Prove2me | Theorems.Thm_Monod_contDiff_and_exists_mulEquiv_GRat_T
-- name    : Monod.contDiff_and_exists_mulEquiv_GRat_T
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-30T14:13:10.643992+00:00
-- url     : https://prove2.me/theorems/0827a75b-49fd-4d0c-ad9b-f2a3577e7370
-- title:
--   p. 2 (Thurston) — G(ℤ) with rational breakpoints consists of C¹ maps of the circle and is conjugate to T
-- statement:
--   Let $G_{\mathbf{Q}}(\mathbf{Z})$ be the group of homeomorphisms of $\mathbf{P}^1$ piecewise in $\mathrm{PSL}_2(\mathbf{Z})$ with breakpoints in $\mathbf{Q} \cup \{\infty\}$ (`GRat`). (i) Each element is $C^1$ as a map of the circle $\mathbf{P}^1$, in its two standard coordinates $t \mapsto t$ and $t \mapsto -1/t$ (with $0 \mapsto \infty$): for each pair of coordinates, on the open set of parameters $t$ where the element sends the point with first coordinate $t$ into the second coordinate patch, the map between the coordinates is $C^1$. (ii) There are a homeomorphism $c$ from the circle $\mathbf{R}/\mathbf{Z}$ to $\mathbf{P}^1$ and an isomorphism $\varphi$ from $G_{\mathbf{Q}}(\mathbf{Z})$ to Thompson's group $T$ with $g \circ c = c \circ \varphi(g)$: conjugation by $c$ carries this group onto $T$.
--
--   **Formalization Note.** The source states for $H(\mathbf{Z})$ with rational breakpoints that "all its elements are automatically $C^1$ and the resulting group is conjugated to $F$", then "The corresponding relation holds between $G(\mathbf{Z})$ and Thompson's group $T$"; both halves are stated here for $G$. Since elements of $G$ move $\infty$, $C^1$ is stated on the whole circle through its two standard charts rather than on $\mathbf{R}$ alone.
-- source:
--   Monod, N., Groups of piecewise projective homeomorphisms, Proc. Natl. Acad. Sci. USA 110 (2013) 4524–4527, https://doi.org/10.1073/pnas.1218426110 (arXiv:1209.5229v2, whose page numbers are used), p. 2, after Problem 12

import Mathlib
import Definitions.Def_CannonFloydParry_T
import Definitions.Def_Monod_PiecewiseProjective

namespace Monod

theorem contDiff_and_exists_mulEquiv_GRat_T :
    (let σ : Fin 2 → ℝ → OnePoint ℝ :=
        ![fun t => (t : OnePoint ℝ),
          fun t => if t = 0 then OnePoint.infty else ((-t⁻¹ : ℝ) : OnePoint ℝ)]
      ∀ g ∈ GRat, ∀ i j : Fin 2, ∃ u : ℝ → ℝ,
        ContDiffOn ℝ 1 u {t | g (σ i t) ∈ Set.range (σ j)} ∧
          ∀ t, g (σ i t) ∈ Set.range (σ j) → g (σ i t) = σ j (u t)) ∧
      ∃ (c : UnitAddCircle ≃ₜ OnePoint ℝ) (φ : GRat ≃* CannonFloydParry.T),
        ∀ (g : GRat) (x : UnitAddCircle),
          (g : OnePoint ℝ ≃ₜ OnePoint ℝ) (c x) = c ((φ g : Equiv.Perm UnitAddCircle) x) := by
  sorry

end Monod
