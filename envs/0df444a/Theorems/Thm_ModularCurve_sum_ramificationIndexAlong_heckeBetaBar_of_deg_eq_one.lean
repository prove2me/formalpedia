-- Prove2me | Theorems.Thm_ModularCurve_sum_ramificationIndexAlong_heckeBetaBar_of_deg_eq_one
-- name    : ModularCurve.sum_ramificationIndexAlong_heckeBetaBar_of_deg_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.908972+00:00
-- url     : https://prove2.me/theorems/e5dd44cb-e436-515d-a6b0-eabd968155df
-- title:
--   Ramification indices along β sum to ℓ+1
-- statement:
--   Fix a natural number $N \neq 0$ and a prime $\ell$ with $\ell \nmid N$, and work over $K = \overline{\mathbb{Q}}$. Write $\bar F_M =$ `modularFunctionFieldBar M` for the intermediate field of $K((q))$ generated over $K$ by the image of the full modular function field of level $M$, and let $\beta =$ `heckeBetaBar` $: \bar F_N \to \bar F_{N\ell}$ be the $K$-algebra map induced by the substitution $q \mapsto q^{\ell}$. Assume: the ring homomorphism underlying $\beta$ is integral (the predicate `HeckeBetaBarIntegral`); every nonzero element of $\bar F_{N\ell}$ has a principal divisor of degree zero, i.e. a divisor whose value at each place is the order of the element there; and every place $W$ of $\bar F_{N\ell}$ over $K$ has degree one, the degree being the $K$-dimension of its residue field. Here a place is a valuation subring containing $K$, different from the whole field, and a principal ideal ring. Then for every place $v$ of $\bar F_N$ over $K$, the sum of the ramification indices $e_{\beta}(W)$ over the places $W$ of $\bar F_{N\ell}$ lying over $v$ along $\beta$ equals $\ell + 1$ in $\mathbb{Z}$, where $e_{\beta}(W)$ is the least positive $n$ of the form $\operatorname{ord}_W(\beta(f))$ for some nonzero $f \in \bar F_N$.
--
--   This is the width bookkeeping for the fibres of the second degeneracy map in the Eichler–Shimura correspondence: since $\ell \nmid N$ the degree of $\bar F_{N\ell}$ over $\beta(\bar F_N)$ is $\ell+1$, and with all residue degrees equal to one the fundamental identity degenerates to a sum of ramification indices. It is used in the place-level computations of the Hecke divisor correspondence, in particular in the analysis of fibres and cusps of the models in characteristic $p$ and in the construction of place specialisation data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_sum_ramificationIndexAlong_heckeBetaBar_of_deg_eq_one.lean

import Definitions.Def_ModularCurve_HeckeOperator

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve ModularCurve

theorem ModularCurve.sum_ramificationIndexAlong_heckeBetaBar_of_deg_eq_one (N ℓ : ℕ) [NeZero N] [Fact ℓ.Prime] (hlN : ¬ ℓ ∣ N) (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N ℓ) [HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * ℓ))] (hdeg1 : ∀ W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * ℓ)), W.deg = 1) (v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) : ∑ W ∈ Place.fiberAlong (heckeBetaBar (AlgebraicClosure ℚ) N ℓ) hβ v, (W.ramificationIndexAlong (heckeBetaBar (AlgebraicClosure ℚ) N ℓ) : ℤ) = ℓ + 1 := by sorry
