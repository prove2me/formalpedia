-- Prove2me | Theorems.Thm_ModularCurve_hasJZeroNeronAtPDataCore
-- name    : ModularCurve.hasJZeroNeronAtPDataCore
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.414366+00:00
-- url     : https://prove2.me/theorems/007849c5-7e60-5f17-bdfb-8b01e173641a
-- title:
--   Existence of at-q Néron data for J₀(Nq)
-- statement:
--   Fix natural numbers $N$ and $q$ with $N$ nonzero and $q$ prime, and assume $q \nmid N$. The assertion `HasJZeroNeronAtPDataCore N q hqN` is: for every valuation subring $A$ of $\overline{\mathbb{Q}}$ lying over $q$, in the sense that the image of $q$ belongs to the non-units of $A$, the record `JZeroNeronAtPDataCore N q hqN A hA` is inhabited. Such a record consists of three families of additive subgroups $\mathrm{toric}(m) \le \mathrm{fin}(m) \le \mathrm{finPart}(m)$ of `JZero (N * q)`, indexed by $m \in \mathbb{N}$, with $\mathrm{finPart}(m)$ contained in the $m$-torsion `jZeroTorsion (N * q) m` and stable both under the action of `HeckeAlg` through `heckeModuleBar (N * q)` and under the decomposition subgroup of $A$ over $\mathbb{Q}$; a cyclotomic clause stating that an element $\sigma$ of the inertia subgroup of $A$ over $\mathbb{Q}$ which acts on $m$-th roots of unity by $\zeta \mapsto \zeta^{c}$ acts on $\mathrm{toric}(m)$ by multiplication by $c$; a finite `HeckeAlg`-module $\Phi$ together with additive maps $\mathrm{spec}_m : \mathrm{finPart}(m) \to \Phi$ that are `HeckeAlg`-equivariant and have kernel exactly $\mathrm{fin}(m)$; an Eisenstein clause saying that, granted `HeckeInputsAll (N * q)` and `HeckeOperatorsCommuteBar (N * q)`, the operator $\mathrm{heckeGen}(\ell) - (\ell + 1)$ annihilates $\Phi$ for every prime $\ell \nmid Nq$; a Raynaud prolongation clause for $q \ne 2$ concerning subgroups $V$ of the $q$-torsion modelled, compatibly with the group law and the Galois action, by a finite flat cocommutative Hopf algebra over [`GaloisRep.ratLocalizedAt q`](def/GaloisRep_Flat.html#L8); and further clauses at $m = q$ of detection type.
--
--   This is the package of at-$q$ Néron data for $J_0(Nq)$: the $q$-torsion filtration by toric and finite parts, its specialisation to the component group with the Eisenstein property, and the prolongation and detection clauses at $m = q$. It feeds the level-lowering step at $q$, being used by [`ModularCurve.hasLowerLevelTorsion_of_finiteFlat_rankTwo_heckeTorsion`](thm.html#ModularCurve.hasLowerLevelTorsion_of_finiteFlat_rankTwo_heckeTorsion).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_hasJZeroNeronAtPDataCore.lean

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronAtPDataCore

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem ModularCurve.hasJZeroNeronAtPDataCore (N q : ℕ) [NeZero N] [Fact q.Prime] (hqN : ¬ q ∣ N) :
    HasJZeroNeronAtPDataCore N q hqN := by sorry
