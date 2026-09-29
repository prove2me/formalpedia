-- Prove2me | Theorems.Thm_ModularCurve_finrankAlong_heckeBetaOneBar
-- name    : ModularCurve.finrankAlong_heckeBetaOneBar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.061738+00:00
-- url     : https://prove2.me/theorems/7008a6f9-e0d7-56a8-970c-32e2c115fb66
-- title:
--   Degree of the q↦ q^ℓ degeneracy map on X₁(M)
-- statement:
--   Let $L$ be a field equipped with a $\mathbb{Q}$-algebra structure, let $M\ge 1$ be a natural number and let $\ell$ be a prime. Write $F_1 =$ `x1FunctionFieldC ℚ M` for the $q$-expansion function field of $X_1(M)$ inside $\mathbb{Q}((q))$, and $F_{1,0} =$ `qExpFunctionFieldC ℚ (Gamma1 M ⊓ Gamma0 (M*ℓ))` for that of $\Gamma_1(M)\cap\Gamma_0(M\ell)$. Assume the hypothesis `HeckeBetaOneDefined M ℓ`: every $y \in F_1$ is carried by the substitution $q \mapsto q^{\ell}$ (the ring endomorphism of $\mathbb{Q}((q))$ obtained by pushing the Hahn-series index along multiplication by $\ell$ on $\mathbb{Z}$) into $F_{1,0}$. Under this hypothesis the $L$-algebra map `heckeBetaOneBar L M ℓ` is the one induced by $q \mapsto q^{\ell}$ from `laurentBaseChange L F₁` to `laurentBaseChange L F₁₀`, where `laurentBaseChange L F₀` denotes the intermediate field of $L((q))$ generated over $L$ by the coefficientwise image of $F_0$. The conclusion is that the target, viewed as a module over the source along this map, has finite rank equal to $\ell$ if $\ell \mid M$, and to $\ell+1$ otherwise.
--
--   This is the degree of the second degeneracy map, induced on function fields by $\tau \mapsto \ell\tau$, from the modular curve of level $\Gamma_1(M)\cap\Gamma_0(M\ell)$ to $X_1(M)$, in its $q$-expansion model base-changed to $L$. Together with the corresponding computation for the first degeneracy map [`ModularCurve.finrankAlong_heckeAlphaOneBar`](thm.html#ModularCurve.finrankAlong_heckeAlphaOneBar), it underlies the construction of the Hecke correspondence $T_\ell$ on $X_1(M)$ and the analysis of its action on Jacobians and Tate modules.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_finrankAlong_heckeBetaOneBar.lean

import Mathlib
import Definitions.Def_ModularCurve_X1HeckeOperator

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.finrankAlong_heckeBetaOneBar (L : Type*) [Field L] [Algebra ℚ L]
    (M : ℕ) [NeZero M] (ℓ : ℕ) [Fact ℓ.Prime] (h : ModularCurve.HeckeBetaOneDefined M ℓ) :
    AlgebraicCurve.finrankAlong L (ModularCurve.heckeBetaOneBar L M ℓ) =
      if ℓ ∣ M then ℓ else ℓ + 1 := by sorry
