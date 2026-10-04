-- Prove2me | Theorems.Thm_Monod_mem_HRat_iff
-- name    : Monod.mem_HRat_iff
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-03T13:32:15.965152+00:00
-- url     : https://prove2.me/theorems/ceea59ee-5fea-40aa-843a-f3268f22089b
-- title:
--   Monod, p. 2 — H(ℤ) with rational breakpoints is exactly the set of its piecewise elements fixing ∞
-- statement:
--   A homeomorphism $f$ of $\mathbf P^1 = \mathbb R \cup \{\infty\}$ lies in `HRat`, the elements of `GRat` fixing $\infty$, exactly when $f$ is piecewise in $\mathrm{PSL}_2(\mathbb Z)$ with all breakpoints in $\mathbb Q \cup \{\infty\}$ (an element of `Gpp` with `IsPiecewiseProjOn ⊥ ratPoints f`) and fixes $\infty$ (`f ∈ fixInf`).
--
--   All names are from the Monod definitions bundle; `⊥` is the subring $\mathbb Z$ of $\mathbb R$. This is `Monod.mem_GRat_iff` intersected with the stabilizer of $\infty$.
--
--   Monod writes on p. 2: “The relation is as follows: if we modify the definition of $H(\mathbf{Z})$ by requiring that the breakpoints be rational, then all its elements are automatically $C^1$ and the resulting group is conjugated to $F$. The corresponding relation holds between $G(\mathbf{Z})$ and Thompson’s group $T$.” This theorem identifies the bundle's `HRat`, defined through a generated subgroup, with the set Monod's sentence describes, the group the published statement `Monod.contDiff_and_exists_mulEquiv_HRat_F` shows to be isomorphic to Thompson's group $F$.
-- source:
--   Monod, N., Groups of piecewise projective homeomorphisms, Proc. Natl. Acad. Sci. USA 110 (2013) 4524–4527, https://doi.org/10.1073/pnas.1218426110 (arXiv:1209.5229v2, whose page numbers are used), p. 2

import Mathlib
import Definitions.Def_Monod_PiecewiseProjective

namespace Monod

theorem mem_HRat_iff (f : OnePoint ℝ ≃ₜ OnePoint ℝ) :
    f ∈ HRat ↔ (f ∈ Gpp ∧ IsPiecewiseProjOn ⊥ ratPoints f) ∧ f ∈ fixInf := by
  sorry

end Monod
