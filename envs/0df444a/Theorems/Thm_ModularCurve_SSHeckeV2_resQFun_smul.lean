-- Prove2me | Theorems.Thm_ModularCurve_SSHeckeV2_resQFun_smul
-- name    : ModularCurve.SSHeckeV2.resQFun_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.379182+00:00
-- url     : https://prove2.me/theorems/3fb474a3-7682-5d94-84be-d788a6d0af09
-- title:
--   Homogeneity of the supersingular restriction resQFun
-- statement:
--   Let $p$ be a prime with $5 \le p$, let $K$ be an algebraically closed field of characteristic $p$, and let $N \ge 1$ satisfy $(N : K) \ne 0$. Let $k$ be an integer, $c \in K$, and let $\varphi$ be a power series over $K$ lying in [`ModPForms.modPMod N k K`](def/CuspForm_ModPForms.html#L12), the $K$-span inside $K[[q]]$ of the series $\sum_n a_n q^n$ obtained from weight-$k$ modular forms $f$ on $\Gamma_0(N)$ whose $q$-expansion coefficients $\mathrm{qCoeff}\, f\, n$ are all integers $a_n$, reduced into $K$. The assertion is that [`ModularCurve.resQFun p N K hp5 k`](def/ModularCurve_SSHeckeV2.html#L42) is homogeneous at $\varphi$: $\mathrm{resQFun}(c \cdot \varphi) = c \cdot \mathrm{resQFun}(\varphi)$, the scalar action on the right being pointwise on the $K$-valued functions on `SSIndex p N K hp5 k`. Here $\mathrm{resQFun}(\psi)$ sends an index $x$ to $x_1.\mathrm{evalAt}\bigl(\mathrm{unif}(x_1)^{a} \cdot G\bigr)$, with $a = \lfloor k/2 \rfloor\bigl(\mathrm{jWidth}(x_1.\mathrm{evalAt}(\mathrm{jGeomGen}))-1\bigr)$ divided by $\mathrm{placeWidth}\, x_1$, and $G$ chosen by `Classical.epsilon` among elements of the field $K(j_q, j_{q,N}) \subseteq K((q))$ whose Laurent series equals $\psi \cdot \theta(j_q)^{-\lfloor k/2 \rfloor}$, where $\theta(f) = q\,f'$.
--
--   This is one half of the statement that the restriction-to-supersingular-points map on mod $p$ weight-$k$ $q$-expansions is $K$-linear; because the auxiliary modular function $G$ is selected by an unspecified choice, homogeneity requires proof rather than following formally. It is used in the construction of the supersingular datum over an algebraically closed field, [`ModPForms.nonempty_ssDatum_algebraicClosure`](thm.html#ModPForms.nonempty_ssDatum_algebraicClosure).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_SSHeckeV2_resQFun_smul.lean

import Mathlib
import Definitions.Def_ModularCurve_SSHeckeV2
import Definitions.Def_CuspForm_ModPForms

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
open AlgebraicCurve ModularCurve

theorem ModularCurve.SSHeckeV2.resQFun_smul (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (K : Type) [Field K] [CharP K p] [IsAlgClosed K] [DecidableEq K] (N : ℕ) [NeZero N]
    (hN : (N : K) ≠ 0) (k : ℤ) (c : K) (φ : PowerSeries K) (hφ : φ ∈ ModPForms.modPMod N k K) :
    ModularCurve.resQFun p N K hp5 k (c • φ) = c • ModularCurve.resQFun p N K hp5 k φ := by sorry
