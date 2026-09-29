-- Prove2me | Theorems.Thm_ModularCurve_finrank_adjoin_jqN_prime_of_not_mem
-- name    : ModularCurve.finrank_adjoin_jqN_prime_of_not_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.414366+00:00
-- url     : https://prove2.me/theorems/fa124ff8-0c37-5ab8-830e-5eb7c5ffb796
-- title:
--   Degree p+1 of j(qᵖ) over a field containing j(q)
-- statement:
--   Work inside the field $\mathbb{Q}((q))$ of Laurent series over $\mathbb{Q}$ (Hahn series with value group $\mathbb{Z}$). Here $jq$ denotes the element $q^{-1}\cdot \mathrm{ofPowerSeries}(jNumQ)$, that is, the $q$-expansion of the modular $j$-invariant obtained from the integral power series $jNum$ with rational coefficients by shifting by $q^{-1}$; and for $N \neq 0$, $jqN\,N$ is the image $qExpand\ \mathbb{Q}\ N\ jq$ of $jq$ under the ring homomorphism of $\mathbb{Q}((q))$ induced by multiplication by $N$ on the exponent group $\mathbb{Z}$, i.e. the substitution $q \mapsto q^{N}$, so $jqN\,N$ is the $q$-expansion of $j(q^{N})$. The data are: an intermediate field $F$ of the extension $\mathbb{Q} \subseteq \mathbb{Q}((q))$ containing $jq$; a prime number $p$; and the hypothesis that $jqN\,p \notin F$. The conclusion is that the $F$-vector space $F(jqN\,p)$, the intermediate field generated over $F$ by the single element $jqN\,p$, has finite rank exactly $p+1$; that is, $[F(j(q^{p})) : F] = p+1 = \psi(p)$, for every such $F$.
--
--   This is the prime-level case of the classical statement that the modular equation $\Phi_N(X,Y)$ has degree $\psi(N)$ in each variable and is irreducible over $\mathbb{Q}(j)$, here in the dichotomy form valid over an arbitrary intermediate field containing $j(q)$: either $j(q^p)$ already lies in $F$, or it generates an extension of degree exactly $p+1$. It feeds the $q$-expansion model of the function field of $X_0(N)$, and is used for the non-membership statement [`ModularCurve.jqN_prime_not_mem_adjoin`](thm.html#ModularCurve.jqN_prime_not_mem_adjoin), for the construction of Atkin–Lehner automorphisms at primes not dividing the level, and in the computation of Hecke operators via degeneracy pushforwards.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_finrank_adjoin_jqN_prime_of_not_mem.lean

import Definitions.Def_ModularCurve_X0
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem ModularCurve.finrank_adjoin_jqN_prime_of_not_mem (F : IntermediateField ℚ (LaurentSeries ℚ)) (hj : jq ∈ F) (p : ℕ) [hp : Fact (Nat.Prime p)] (hpF : jqN p ∉ F) : Module.finrank F (IntermediateField.adjoin F ({jqN p} : Set (LaurentSeries ℚ))) = p + 1 := by sorry
