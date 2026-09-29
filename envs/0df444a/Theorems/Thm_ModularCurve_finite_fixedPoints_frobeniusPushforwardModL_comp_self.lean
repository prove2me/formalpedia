-- Prove2me | Theorems.Thm_ModularCurve_finite_fixedPoints_frobeniusPushforwardModL_comp_self
-- name    : ModularCurve.finite_fixedPoints_frobeniusPushforwardModL_comp_self
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.061738+00:00
-- url     : https://prove2.me/theorems/6f29e423-b2d3-5443-8a57-cea675ba5726
-- title:
--   Finiteness of fixed points of the squared Frobenius push-forward
-- statement:
--   Let $\ell$ be a prime, let $K$ be an algebraically closed field of characteristic $\ell$, and assume that every $a \in K$ satisfies $a^{\ell^{n}} = a$ for some $n > 0$ (so that $K$ is an algebraic closure of $\mathbf{F}_\ell$); let $N$ be a positive integer. Write $\mathrm{JZeroC}\,K\,N$ for `JZeroC K N`, the degree-zero divisor class group $\mathrm{Pic}^0$ of the full level-$N$ modular function field `modularFunctionFieldFullC K N` over $K$, and let $T =$ `frobeniusPushforwardModL K N ℓ` be the endomorphism of this group defined as follows: if the predicate `FrobeniusInputsModL K N ℓ` holds — that is, if divisors of the modular function field have the principal-divisor property, the map `frobeniusModL K N ℓ` is finite along the relevant extension, and it satisfies the fundamental identity and the norm formula — then $T$ is the map induced on $\mathrm{Pic}^0$ by push-forward of degree-zero divisors along `frobeniusModL K N ℓ`, and otherwise $T = 0$. The assertion is that the set of fixed points of the composite $T \circ T$, i.e. $\{x : T(T(x)) = x\}$, is finite.
--
--   This is the finiteness, for the reduction modulo $\ell$ of the Jacobian of the modular curve of level $N$, of the group of points fixed by the square of Frobenius — the analogue of the finiteness of the group of $\mathbf{F}_{\ell^2}$-rational points of an abelian variety over a finite field. It is used to show that the relevant Tate module statement forces vanishing, and is transported to the Néron model picture at $p$ in [`ModularCurve.JZeroNeronObjectAtP.finite_fixedPoints_frobSp_comp_self`](thm.html#ModularCurve.JZeroNeronObjectAtP.finite_fixedPoints_frobSp_comp_self).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_finite_fixedPoints_frobeniusPushforwardModL_comp_self.lean

import Definitions.Def_ModularCurve_FrobeniusModL

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem ModularCurve.finite_fixedPoints_frobeniusPushforwardModL_comp_self
    (K : Type*) [Field K] [IsAlgClosed K] {ℓ : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
    (halg : ∀ a : K, ∃ n : ℕ, 0 < n ∧ a ^ ℓ ^ n = a) (N : ℕ) [NeZero N] :
    (Function.fixedPoints
      (frobeniusPushforwardModL K N ℓ ∘ frobeniusPushforwardModL K N ℓ)).Finite := by sorry
