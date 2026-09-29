-- Prove2me | Theorems.Thm_ModularCurve_SSHeckeV2_exists_linearEquiv_ssCarrier_forall_ssHeckeFun_eq_smul
-- name    : ModularCurve.SSHeckeV2.exists_linearEquiv_ssCarrier_forall_ssHeckeFun_eq_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.379182+00:00
-- url     : https://prove2.me/theorems/87e2f868-05ef-5abd-9b9f-73ea33decbbe
-- title:
--   A weight ladder S_k ≃ S_{k+p+1} twisting Hecke by ℓ
-- statement:
--   Let $p$ be a prime with $p \ge 5$, let $K$ be an algebraically closed field of characteristic $p$, let $N \ge 1$ with $(N : K) \neq 0$, and let $k \in \mathbb{Z}$ with $1 \le k$. For a weight $m \in \mathbb{Z}$, [`ModularCurve.SSIndex p N K hp5 m`](def/ModularCurve_SSCarrier.html#L13) is the subtype of places $x$ of the field `modularFunctionFieldC K N` over $K$ satisfying $x \in$ `ssPlaces p N K`, $2 \le m$, $2 \mid m$, `placeWidth N x` $\mid m/2$ and $5 \le p$, and the carrier `SSCarrier p N K hp5 m` is the $K$-vector space of all functions from this index type to $K$; in particular both carriers below are trivial when $k$ is odd. The assertion is that there exists a $K$-linear isomorphism $e$ from `SSCarrier p N K hp5 k` onto `SSCarrier p N K hp5 (k + (p+1))` such that for every prime $\ell$ with $\ell \nmid N$ and $\ell \neq p$, and every $v$ in the weight-$k$ carrier, $$\mathrm{ssHeckeFun}_{k+p+1,\ell}(e\,v) \;=\; (\ell : K) \cdot e\bigl(\mathrm{ssHeckeFun}_{k,\ell}(v)\bigr).$$ Here `ssHeckeFun p N K hp5 m ℓ v` is the function sending an index $x$ to $\ell^{m/2-1}$ times `lead N K x.1 (poleOrder p N K hp5 m x)` — the value at $x$ of the product of the $(\,\cdot\,)$-th power of the chosen uniformiser at $x$ with the argument, the exponent being $(m/2)\,(\,$`jWidth`$(x.\mathrm{evalAt}\,$`jGeomGen K N`$) - 1)/\,$`placeWidth N x` — applied to the trace from `charLDegeneracyRoof K N ℓ` down to `modularFunctionFieldC K N` of `heckeBetaC K N ℓ (liftFun p N K hp5 m v)` times the $(m/2)$-th power of `heckeMultiplier N K ℓ`, where `liftFun` chooses a function in `modularFunctionFieldC K N` whose order at each supersingular place is bounded below by minus the corresponding coefficient of `weightDivisor K N (m/2).toNat` and whose leading coefficients at the indices reproduce $v$.
--
--   This is the weight ladder of the supersingular datum: multiplication by (the leading coefficients at the supersingular places of a function representing) $E_{p+1} \bmod p$ identifies weight-$k$ with weight-$(k+p+1)$ supersingular values, semilinearly for the Hecke action in the sense that $T_\ell$ is scaled by $\ell$. It is used in the construction of a supersingular datum over an algebraically closed field, in [`ModPForms.nonempty_ssDatum_algebraicClosure`](thm.html#ModPForms.nonempty_ssDatum_algebraicClosure).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_SSHeckeV2_exists_linearEquiv_ssCarrier_forall_ssHeckeFun_eq_smul.lean

import Mathlib
import Definitions.Def_ModularCurve_SSCarrier
import Definitions.Def_ModularCurve_SSHeckeV2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
open AlgebraicCurve ModularCurve

theorem ModularCurve.SSHeckeV2.exists_linearEquiv_ssCarrier_forall_ssHeckeFun_eq_smul
    (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (K : Type) [Field K] [CharP K p] [IsAlgClosed K] [DecidableEq K] (N : ℕ) [NeZero N]
    (hN : (N : K) ≠ 0) (k : ℤ) (hk : 1 ≤ k) :
    ∃ e : ModularCurve.SSCarrier p N K hp5 k ≃ₗ[K] ModularCurve.SSCarrier p N K hp5 (k + ((p : ℤ) + 1)),
      ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ¬ ℓ ∣ N → ℓ ≠ p →
        ∀ v : ModularCurve.SSCarrier p N K hp5 k,
          haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
          ModularCurve.ssHeckeFun p N K hp5 (k + ((p : ℤ) + 1)) ℓ (e v)
            = (ℓ : K) • e (ModularCurve.ssHeckeFun p N K hp5 k ℓ v) := by sorry
