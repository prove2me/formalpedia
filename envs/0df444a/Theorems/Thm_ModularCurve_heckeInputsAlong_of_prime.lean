-- Prove2me | Theorems.Thm_ModularCurve_heckeInputsAlong_of_prime
-- name    : ModularCurve.heckeInputsAlong_of_prime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.700479+00:00
-- url     : https://prove2.me/theorems/1b8349a3-d3da-56f0-95a9-d98cd6071cce
-- title:
--   Hecke correspondence inputs at every level and prime ℓ
-- statement:
--   Let $L$ be a field equipped with a $\mathbb{Q}$-algebra structure, let $N \geq 1$ be a natural number and let $\ell$ be a prime. Then [`ModularCurve.HeckeInputsAlong L N ℓ`](def/ModularCurve_HeckeOperatorTotal.html#L13) holds, i.e. all of the following are satisfied for the two degeneracy embeddings $\alpha =$ `heckeAlphaBar L N ℓ` (the inclusion coming from monotonicity of $N \mapsto$ `laurentBaseChange L (modularFunctionFieldFull N)` along $N \mid N\ell$) and $\beta =$ `heckeBetaBar L N ℓ` (induced by $q \mapsto q^{\ell}$ on Laurent series), both regarded as $L$-algebra maps from `laurentBaseChange L (modularFunctionFieldFull N)` to `laurentBaseChange L (modularFunctionFieldFull (N * ℓ))`, where `modularFunctionFieldFull M` is the subfield of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by `divisorExpansions M` and `laurentBaseChange L` is the subfield of $L((q))$ generated over $L$ by the coefficientwise image of such a subfield: the underlying ring map of $\alpha$ is integral; the underlying ring map of $\beta$ is integral; the field `laurentBaseChange L (modularFunctionFieldFull (N * ℓ))` has principal divisors over $L$, that is, every nonzero element $f$ admits a divisor $D$ of degree $0$ with $D(v) = v.\mathrm{ord}(f)$ at every place $v$; the target is a finite module over the source via $\alpha$; the fundamental identity holds for the extension along $\beta$; and the pushforward norm formula for divisors holds for the finite extension along $\alpha$. In particular $\ell \mid N$ is allowed.
--
--   This packages the hypotheses needed to define the Hecke correspondence $T_{\ell} = \alpha_{*}\beta^{*}$ attached to the pair of degeneracy maps $X_0(N\ell) \to X_0(N)$, on divisors and on the degree-zero divisor class group, and asserts that they are unconditionally available at every level $N$ and every prime $\ell$. It is the input consumed by the construction of the Hecke operators on $J_0(N)$ and by the many later statements about their action, including on component groups and on $\ell$-divisibility of $J_0(N)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_heckeInputsAlong_of_prime.lean

import Definitions.Def_ModularCurve_HeckeOperatorTotal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.heckeInputsAlong_of_prime (L : Type*) [Field L] [Algebra ℚ L] (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime] : ModularCurve.HeckeInputsAlong L N ℓ := by sorry
