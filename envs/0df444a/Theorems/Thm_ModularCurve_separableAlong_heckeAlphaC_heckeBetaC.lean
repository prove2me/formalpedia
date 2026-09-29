-- Prove2me | Theorems.Thm_ModularCurve_separableAlong_heckeAlphaC_heckeBetaC
-- name    : ModularCurve.separableAlong_heckeAlphaC_heckeBetaC
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.618386+00:00
-- url     : https://prove2.me/theorems/8b27d13d-4323-5737-86ab-316fb5c0cbe1
-- title:
--   Igusa separability of the level-q degeneracy maps mod ℓ
-- statement:
--   Let $k$ be an algebraically closed field of prime characteristic $\ell$, and let $N$ and $q$ be nonzero natural numbers with $q$ prime and $\ell \nmid Nq$. Inside the field $k((X))$ of Laurent series over $k$, let $C =$ `modularFunctionFieldC k N` be the intermediate field obtained by adjoining to $k$ the two Laurent series `jqModC k` and `jqNModC k N`, and let $R =$ `charLDegeneracyRoof k N q` be the intermediate field obtained by adjoining to $k$ the four Laurent series `jqModC k`, `jqNModC k N`, `jqNModC k q` and `jqNModC k (N * q)`. Two $k$-algebra maps $C \to R$ are in play: `heckeAlphaC k N q`, the inclusion coming from $C \subseteq R$, and `heckeBetaC k N q`, induced by the ring endomorphism `qExpand k q` of $k((X))$ that multiplies all Hahn-series exponents by $q$ (substitution $X \mapsto X^{q}$), which carries $C$ into $R$. The assertion is that, for each of these two maps used as the structure map making $R$ an algebra over $C$, the resulting extension $R/C$ is separable in the sense of `Algebra.IsSeparable`.
--
--   This is Igusa's separability of the modular correspondence of prime degree $q$ in characteristic $\ell \neq q$, here for the two level-$q$ degeneracy maps between the reduced $q$-expansion fields of levels $N$ and $Nq$. Combined with the finiteness of $R$ over $C$ along both maps ([`ModularCurve.finiteAlong_heckeAlphaC`](thm.html#ModularCurve.finiteAlong_heckeAlphaC) and [`ModularCurve.finiteAlong_heckeBetaC`](thm.html#ModularCurve.finiteAlong_heckeBetaC)), it supplies the fundamental identity $\sum_{w \mid v} e(w\mid v) f(w\mid v) = [R:C]$ needed to compare fibre divisors of the two degeneracy maps, and it is invoked in the mod-$\ell$ analysis of the Hecke correspondence $T_q$ and in the semistable specialisation statements that use it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_separableAlong_heckeAlphaC_heckeBetaC.lean

import Mathlib
import Definitions.Def_ModularCurve_CharLDegeneracyHecke

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve

theorem ModularCurve.separableAlong_heckeAlphaC_heckeBetaC
    (k : Type*) [Field k] [IsAlgClosed k] {ℓ : ℕ} [Fact ℓ.Prime] [CharP k ℓ]
    (N q : ℕ) [NeZero N] [NeZero q] [Fact q.Prime] (hℓ : ¬ ℓ ∣ N * q) :
    SeparableAlong k (heckeAlphaC k N q) ∧ SeparableAlong k (heckeBetaC k N q) := by sorry
