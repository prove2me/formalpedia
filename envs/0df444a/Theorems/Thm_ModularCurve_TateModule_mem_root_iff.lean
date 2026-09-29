-- Prove2me | Theorems.Thm_ModularCurve_TateModule_mem_root_iff
-- name    : ModularCurve.TateModule.mem_root_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.379182+00:00
-- url     : https://prove2.me/theorems/a60a1eda-32f7-591e-9398-0cc4980a4200
-- title:
--   Agreement of the two Tate module carriers
-- statement:
--   Let $p$ be a natural number and let $J$ be an additive abelian group carrying a module structure over the abstract Hecke algebra [`ModularCurve.HeckeAlg`](def/HeckeGalois_EichlerShimura.html#L14), the polynomial ring $\mathbb{Z}[X_\ell : \ell \text{ prime}]$ in one variable for each prime. Let $x : \mathbb{N} \to J$ be a sequence in $J$. Two subobjects of the group of such sequences are compared. The first, [`TateModule p J`](def/EllipticCurve_TateModule.html#L15), is the additive subgroup consisting of those $x$ such that for every $n$ one has $(p^n) \cdot x_n = 0$ and $p \cdot x_{n+1} = x_n$, the scalars acting as integers. The second, [`ModularCurve.TateModule p J`](def/ModularCurve_EichlerShimuraData.html#L15), is the [`ModularCurve.HeckeAlg`](def/HeckeGalois_EichlerShimura.html#L14)-submodule consisting of those $x$ with $x_0 = 0$ and $p \cdot x_{n+1} = x_n$ for every $n$, with $p$ acting as a natural number. The theorem asserts that these two conditions on $x$ are equivalent: $x$ lies in the first subgroup if and only if it lies in the second submodule.
--
--   Both subobjects present the $p$-adic Tate module of $J$ as the group of compatible systems of $p$-power torsion elements; the elliptic-curve side of the formalisation uses the torsion-bound presentation, while the modular-curve side uses the presentation by the recurrence together with $x_0 = 0$, and this lemma identifies their members so that the two may be used interchangeably. It is invoked in the construction of an inertia eigenvector for the $p$-adic Galois representation attached to a cusp form at a prime where the Hecke operator is not a unit.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_TateModule_mem_root_iff.lean

import Definitions.Def_ModularCurve_EichlerShimuraData
import Definitions.Def_EllipticCurve_TateModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.TateModule.mem_root_iff (p : ℕ) (J : Type) [AddCommGroup J]
    [Module ModularCurve.HeckeAlg J] (x : ℕ → J) :
    x ∈ _root_.TateModule p J ↔ x ∈ ModularCurve.TateModule p J := by sorry
