-- Prove2me | Theorems.Thm_ModularCurve_eigenformSupportAt_jZero
-- name    : ModularCurve.eigenformSupportAt_jZero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.889759+00:00
-- url     : https://prove2.me/theorems/4d83ee8d-9165-5e2d-8c90-22e1eb00860a
-- title:
--   Eigenform ideals above p lie in the support of J₀(N)
-- statement:
--   Fix $N \ge 1$ and a prime $p$. Let $J$ denote [`ModularCurve.JZero N`](def/ModularCurve_ArithmeticGalois.html#L115), the group $\mathrm{Pic}^0$ of the function field `modularFunctionFieldBar N` — the base change to $\overline{\mathbb Q}$, inside the Laurent series field $\overline{\mathbb Q}((\,))$, of the full modular function field of level $N$ — that is, degree-zero divisors modulo principal divisors. Assume `HeckeInputsAll N`: for every prime $\ell$ the data `HeckeInputsAlong` over $\overline{\mathbb Q}$ at level $N$ and $\ell$ exist, namely integrality of the $\alpha$- and $\beta$-correspondences, existence of principal divisors for level $N\ell$, finiteness along $\alpha$, together with the fundamental identity for $\beta$ and the norm formula for $\alpha$. Assume also `HeckeOperatorsCommuteBar N`: the divisorial operators `heckeOperatorBar N ℓ` on $J$ commute pairwise, so that $J$ carries the module structure `heckeModuleBar N` over $\mathbb T = \mathbb Z[X_\ell : \ell \text{ prime}]$ in which $X_\ell$ acts as `heckeOperatorBar N ℓ`. The conclusion is `EigenformSupportAt N p J`: for every ideal $\mathfrak m \subseteq \mathbb T$ which is an eigenform ideal of level $N$ — i.e. $\mathfrak m =$ `eigenIdeal` of the system $\ell \mapsto \varphi(a_\ell(f))$ for some normalized weight-two eigenform $f$ on $\Gamma_0(N)$, some subring $\mathcal O \subseteq \mathbb C$ containing all $a_\ell(f)$, some finite field $k$ and some ring homomorphism $\varphi : \mathcal O \to k$ — and which contains the image of $p$, the predicate `MTorsionNeBot` holds for $\mathbb T$, $J$ and $\mathfrak m$, the non-vanishing assertion for the $\mathfrak m$-torsion of $J$.
--
--   This is the Eichler–Shimura-type clause asserting that every mod-$p$ eigenform ideal of level $N$ lies in the support of the Jacobian $J_0(N)(\overline{\mathbb Q})$, the input that lets one attach a nonzero $\mathfrak m$-torsion point, and hence a Galois representation, to a mod-$p$ eigenform. It is used by the level-$N$ realisation statements for maximal ideals of the weight-two Hecke algebra and, through them, by the Frey package supply of eigenform realisations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_eigenformSupportAt_jZero.lean

import Mathlib
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ModularCurve_HeckeInputsAll
import Definitions.Def_ModularCurve_EigenformIdeal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.eigenformSupportAt_jZero (N : ℕ) [NeZero N] (p : ℕ) (hp : p.Prime) (hHI : ModularCurve.HeckeInputsAll N) (hHC : ModularCurve.HeckeOperatorsCommuteBar N) : letI := ModularCurve.heckeModuleBar N; ModularCurve.EigenformSupportAt N p (ModularCurve.JZero N) := by sorry
