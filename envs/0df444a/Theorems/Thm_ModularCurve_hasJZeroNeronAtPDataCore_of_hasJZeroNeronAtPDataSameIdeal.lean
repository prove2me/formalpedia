-- Prove2me | Theorems.Thm_ModularCurve_hasJZeroNeronAtPDataCore_of_hasJZeroNeronAtPDataSameIdeal
-- name    : ModularCurve.hasJZeroNeronAtPDataCore_of_hasJZeroNeronAtPDataSameIdeal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.414366+00:00
-- url     : https://prove2.me/theorems/0c7bfcd3-1f40-5e75-83eb-34901257d946
-- title:
--   Same-ideal at-q Néron data yields the core data
-- statement:
--   Let $N$ and $q$ be natural numbers with $N \neq 0$ and $q$ prime, and suppose $q \nmid N$. The hypothesis is `HasJZeroNeronAtPDataSameIdeal N q hqN`: for every valuation subring $A$ of $\overline{\mathbb{Q}}$ with $q$ a nonunit of $A$, there exists a `JZeroNeronAtPDataSameIdeal` structure for $N$, $q$ and $A$, that is, a `JZeroNeronAtPData` for these data together with the further clause that, under the Hecke input and commutation hypotheses at levels $Nq$ and $N$, for every maximal ideal $\mathfrak{m}$ of `HeckeAlg` containing $q$ but not the generator attached to $q$, the existence of an element of `fin q` lying in the $\mathfrak{m}$-Hecke-torsion of $\mathrm{JZero}(Nq)$ and outside `toric q` forces the $\mathfrak{m}$-Hecke-torsion of $\mathrm{JZero}(N)$ to be nonzero. The conclusion is `HasJZeroNeronAtPDataCore N q hqN`: for every such $A$ there exists a `JZeroNeronAtPDataCore` structure, consisting of three families of subgroups `toric m` $\le$ `fin m` $\le$ `finPart m` of $\mathrm{JZero}(Nq)$ with `finPart m` inside the $m$-torsion and stable under the Hecke algebra and under the decomposition subgroup of $A$ over $\mathbb{Q}$, with inertia acting on `toric m` through the $m$-th cyclotomic character, together with a finite `HeckeAlg`-module $\Phi$ and specialisation maps `finPart m` $\to \Phi$ whose kernels are `fin m` and which are Hecke-equivariant, an Eisenstein condition on $\Phi$, and a Raynaud-type clause for $q \neq 2$.
--
--   This is the forgetful projection from the full at-$q$ Néron carrier for $J_0(Nq)$ carrying the same-ideal level-lowering clause to the core carrier read by the downstream arguments; it is used by [`ModularCurve.hasJZeroNeronAtPDataCore`](thm.html#ModularCurve.hasJZeroNeronAtPDataCore).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_hasJZeroNeronAtPDataCore_of_hasJZeroNeronAtPDataSameIdeal.lean

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronAtPDataCore

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem ModularCurve.hasJZeroNeronAtPDataCore_of_hasJZeroNeronAtPDataSameIdeal (N q : ℕ) [NeZero N] [Fact q.Prime]
    (hqN : ¬ q ∣ N) (h : HasJZeroNeronAtPDataSameIdeal N q hqN) : HasJZeroNeronAtPDataCore N q hqN := by sorry
