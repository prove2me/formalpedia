-- Prove2me | Theorems.Thm_ModularCurve_SSHeckeV2_resQFun_add
-- name    : ModularCurve.SSHeckeV2.resQFun_add
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.379182+00:00
-- url     : https://prove2.me/theorems/fb88bb27-b0b7-559f-9c2b-2c758bb08107
-- title:
--   Additivity of the supersingular restriction map resQFun
-- statement:
--   Let $p$ be a prime with $5 \le p$, let $K$ be an algebraically closed field of characteristic $p$, let $N$ be a nonzero natural number with $(N : K) \neq 0$, let $k$ be an integer, and let $\varphi, \psi$ be power series over $K$ lying in [`ModPForms.modPMod N k K`](def/CuspForm_ModPForms.html#L12), the $K$-span inside $K[[q]]$ of those series $\mathrm{mk}\,(n \mapsto (a_n : K))$ arising from a modular form $f$ of weight $k$ on $\Gamma_0(N)$ all of whose $q$-expansion coefficients $\mathrm{qCoeff}\,f\,n$ are the integers $a_n$. The assertion is that [`ModularCurve.resQFun`](def/ModularCurve_SSHeckeV2.html#L42) is additive on such elements: $\mathrm{resQFun}(\varphi + \psi) = \mathrm{resQFun}\,\varphi + \mathrm{resQFun}\,\psi$ as functions on `SSIndex p N K hp5 k`, addition on the right being pointwise in $K$. Here $\mathrm{resQFun}\,\varphi$ sends an index $x$ to $\mathrm{lead}$ of the place $x.1$ in degree $\mathrm{poleOrder}\,x = \lfloor k/2\rfloor\,(\mathrm{jWidth}(x.1.\mathrm{evalAt}(\mathrm{jGeomGen}\,K\,N)) - 1)$ divided by $\mathrm{placeWidth}\,N\,x.1$, evaluated at an element $G$ of the subfield $K(\bar\jmath_1, \bar\jmath_N) \subseteq \mathrm{LaurentSeries}\,K$ chosen, via `Classical.epsilon`, so that $G$ equals $\varphi$ times $(\theta\,\bar\jmath)^{-\lfloor k/2\rfloor}$ as a Laurent series; $\mathrm{lead}\,x\,a\,G$ is the value of $\mathrm{unif}\,N\,K\,x^{\,a}\cdot G$ at $x$.
--
--   This is the additivity half of the linearity of the restriction of mod-$p$ modular forms of weight $k$ and level $N$ to the supersingular points, expressed on the level of $q$-expansions and leading coefficients at the places indexed by `SSIndex`. It is used in the construction of the supersingular datum over an algebraically closed field, [`ModPForms.nonempty_ssDatum_algebraicClosure`](thm.html#ModPForms.nonempty_ssDatum_algebraicClosure).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_SSHeckeV2_resQFun_add.lean

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

theorem ModularCurve.SSHeckeV2.resQFun_add (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (K : Type) [Field K] [CharP K p] [IsAlgClosed K] [DecidableEq K] (N : ℕ) [NeZero N]
    (hN : (N : K) ≠ 0) (k : ℤ) (φ ψ : PowerSeries K)
    (hφ : φ ∈ ModPForms.modPMod N k K) (hψ : ψ ∈ ModPForms.modPMod N k K) :
    ModularCurve.resQFun p N K hp5 k (φ + ψ) = ModularCurve.resQFun p N K hp5 k φ + ModularCurve.resQFun p N K hp5 k ψ := by sorry
