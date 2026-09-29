-- Prove2me | Theorems.Thm_ModPForms_exists_isModPFormFn_qexpOfWeight_eq_of_mem_modPMod
-- name    : ModPForms.exists_isModPFormFn_qexpOfWeight_eq_of_mem_modPMod
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.70306+00:00
-- url     : https://prove2.me/theorems/759f463d-8e32-546e-a671-081a3c9b0624
-- title:
--   Mod p forms of weight 2m come from modular functions
-- statement:
--   Let $p$ be a prime, $N \ge 1$ with $p \nmid N$, let $K$ be a field of characteristic $p$, let $m$ be a natural number, and let $\varphi \in K[[q]]$ belong to [`ModPForms.modPMod N (2*m) K`](def/CuspForm_ModPForms.html#L12), the $K$-span of those power series $\sum_n \bar a_n q^n$ obtained by reducing into $K$ an integer sequence $(a_n)$ which occurs as the $q$-expansion coefficient sequence of some modular form $f$ of weight $2m$ on $\Gamma_0(N)$, i.e. $\mathrm{qCoeff}\,f\,n = a_n$ in $\mathbb{C}$ for all $n$. Then there is an element $G$ of the intermediate field $\mathrm{modularFunctionFieldC}\,K\,N = K(\bar j(q), \bar j(q^N)) \subseteq K((q))$, where $\bar j(q) =$ `jqModC K` is $q^{-1}$ plus the reduction to $K$ of the integral part of the $j$-expansion and $\bar j(q^N)$ is its $q \mapsto q^N$ substitution, such that: (i) $G$ satisfies `IsModPFormFn K m`, namely $G^6 \bar j^{4m} (\bar j - 1728)^{3m}$ is integral over $K[\bar j]$ and $G^2 \bar j^{m} (\bar j - 1728)^{m}$ is integral over $K[\bar j^{-1}]$; and (ii) $G \cdot (\theta \bar j)^m = \varphi$ in $K((q))$, where $\theta \bar j =$ `thetaJ K` and $\varphi$ is viewed in $K((q))$.
--
--   This is the elementary direction of the comparison between the $q$-expansions of classical modular forms reduced mod $p$ and geometric (Katz-style) mod $p$ modular forms of weight $2m$ on $X_0(N)$, presented here as a weight-$2m$ $q$-expansion identity $G\cdot(\theta\bar j)^m = \varphi$ for a modular function $G$ subject to the two integrality conditions at the cusps $j = \infty$ and $j = 0, 1728$. It is used by the results producing mod $p$ forms from such functions and, via its companion in the opposite direction, in the passage between classical mod $p$ modular forms and the function-field description of level structure.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModPForms_exists_isModPFormFn_qexpOfWeight_eq_of_mem_modPMod.lean

import Mathlib
import Definitions.Def_CuspForm_ModPForms
import Definitions.Def_ModularCurve_ModPFormFn

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve

theorem ModPForms.exists_isModPFormFn_qexpOfWeight_eq_of_mem_modPMod
    (p : ℕ) [Fact p.Prime] (N : ℕ) [NeZero N] (hpN : ¬ p ∣ N)
    (K : Type) [Field K] [CharP K p] (m : ℕ)
    (φ : PowerSeries K) (hφ : φ ∈ ModPForms.modPMod N (2 * (m : ℤ)) K) :
    ∃ G : ↥(modularFunctionFieldC K N),
      IsModPFormFn K m (G : LaurentSeries K) ∧
      qexpOfWeight K (m : ℤ) (G : LaurentSeries K) = HahnSeries.ofPowerSeries ℤ K φ := by sorry
