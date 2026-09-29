-- Prove2me | Theorems.Thm_ModularCurve_exists_isFrickeAutFull
-- name    : ModularCurve.exists_isFrickeAutFull
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.903374+00:00
-- url     : https://prove2.me/theorems/15ca057b-f5a1-5d87-b099-8eae7183423f
-- title:
--   Fricke automorphism of ℚ(j(qᵈ):d∣ℓ) at prime level
-- statement:
--   Let $\ell$ be a natural number carrying the instance that it is prime. The field in play is `modularFunctionFieldFull ℓ`, the intermediate field of $\mathbb{Q} \subseteq \mathbb{Q}((q))$ (Laurent series over $\mathbb{Q}$) obtained by adjoining to $\mathbb{Q}$ the set of Laurent series $\mathrm{qExpand}\,\mathbb{Q}\,d\ (\mathrm{jq})$ for all nonzero $d$ dividing $\ell$, where `jq` is the distinguished Laurent series playing the role of the $q$-expansion of $j$ and `qExpand ℚ d` is the ring homomorphism of Laurent series that multiplies all exponents by $d$ (substitution $q \mapsto q^{d}$). The assertion is that there exists a $\mathbb{Q}$-algebra automorphism $\sigma$ of this field satisfying `IsFrickeAutFull ℓ σ`, that is: for all natural numbers $a, b$ with $a \cdot b = \ell$, both nonzero, $\sigma$ carries the element of `modularFunctionFieldFull ℓ` given by $\mathrm{qExpand}\,\mathbb{Q}\,a\ (\mathrm{jq})$ (together with its membership witness, coming from $a \mid \ell$) to the element given by $\mathrm{qExpand}\,\mathbb{Q}\,b\ (\mathrm{jq})$. No further conditions on $\sigma$ are imposed, and no claim of uniqueness or of $\sigma$ being an involution is made.
--
--   This is the existence of the Fricke involution $w_\ell$, $\tau \mapsto -1/(\ell\tau)$, in its function-field form: an automorphism of the function field of $X_0(\ell)$ interchanging $j$ and $j(\ell\,\cdot)$, stated for the divisor-generated presentation $\mathbb{Q}(j(q^{d}) : d \mid \ell)$. It feeds the Atkin–Lehner input used downstream in the analysis of values and poles of modular functions at points of $X_0(\ell)$, including the treatment of nodes and of Frobenius node pairs.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_isFrickeAutFull.lean

import Definitions.Def_ModularCurve_AtkinLehner

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve IntermediateField

theorem ModularCurve.exists_isFrickeAutFull (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] : ∃ σ : modularFunctionFieldFull ℓ ≃ₐ[ℚ] modularFunctionFieldFull ℓ, IsFrickeAutFull ℓ σ := by sorry
