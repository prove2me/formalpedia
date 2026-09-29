-- Prove2me | Theorems.Thm_ModularCurve_diamondAut_congr_and_mul_and_one_and_inv_and_diamondAutBar
-- name    : ModularCurve.diamondAut_congr_and_mul_and_one_and_inv_and_diamondAutBar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.889759+00:00
-- url     : https://prove2.me/theorems/500d9b50-5b52-5d6a-8a0f-c417b0d17e19
-- title:
--   Diamond automorphisms of ℚ(X₁(N)) form a (ℤ/N)^×-action
-- statement:
--   Let $N$ be a nonzero natural number. Write $F =$ [`ModularCurve.x1FunctionField N`](def/ModularCurve_X1.html#L137) for the intermediate field `qExpFunctionFieldC ℚ (Gamma1 N)` of $\mathbb{Q}((q))$, and $\bar F =$ [`ModularCurve.x1FunctionFieldBar N`](def/ModularCurve_X1.html#L182) for the intermediate field of $\overline{\mathbb{Q}}((q))$ obtained by adjoining to $\overline{\mathbb{Q}}$ the image of $F$ under the coefficientwise embedding. For $d\in\mathbb{N}$, [`ModularCurve.diamondAut N d`](def/ModularCurve_X1Diamond.html#L66) is a choice of $\mathbb{Q}$-algebra automorphism $\sigma$ of $F$ satisfying `IsDiamondAut N d σ` — namely $d$ is coprime to $N$ and, for every weight $k$, all modular forms $f,g$ of level $\Gamma_1(N)$ and weight $k$ with integral $q$-expansions $p_f,p_g$ and $p_g\neq 0$ as a series over $\mathbb{Q}$, and every $\gamma\in\Gamma_0(N)$ whose upper-left entry reduces to $d$ in $\mathbb{Z}/N$, one has $\sigma(f/g)\cdot (g|_k\gamma) = f|_k\gamma$ on $q$-expansions over $\mathbb{C}$ — and the identity when no such $\sigma$ exists; [`ModularCurve.diamondAutBar N d`](def/ModularCurve_X1Diamond.html#L94) is the corresponding base-changed automorphism of $\bar F$ over $\overline{\mathbb{Q}}$. The theorem asserts eight statements: for $d,d'$ coprime to $N$, the automorphism depends only on the class of $d$ in $\mathbb{Z}/N$; $\langle dd'\rangle x = \langle d\rangle\langle d'\rangle x$ for all $x$; $\langle 1\rangle$ is the identity automorphism; and $\langle d\rangle\langle d'\rangle x = x$ whenever $dd'\equiv 1 \pmod N$ — each both for `diamondAut` on $F$ and for `diamondAutBar` on $\bar F$.
--
--   These are the defining properties of the diamond operators $\langle d\rangle$ on the function field of $X_1(N)$, packaging them into an action of $(\mathbb{Z}/N)^\times$ both over $\mathbb{Q}$ and after base change to $\overline{\mathbb{Q}}$. They are used in the analysis of the reduction of $X_1(N)$ and of the interaction of diamond operators with Atkin–Lehner involutions and Frobenius.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_diamondAut_congr_and_mul_and_one_and_inv_and_diamondAutBar.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_X1HeckeOperator
import Definitions.Def_ModularCurve_X1Diamond

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.diamondAut_congr_and_mul_and_one_and_inv_and_diamondAutBar
    (N : ℕ) [NeZero N] :

    (∀ d d' : ℕ, d.Coprime N → d'.Coprime N → ((d : ZMod N) = (d' : ZMod N)) →
      ModularCurve.diamondAut N d = ModularCurve.diamondAut N d') ∧

    (∀ d d' : ℕ, d.Coprime N → d'.Coprime N →
      ∀ x : ↥(ModularCurve.x1FunctionField N),
        ModularCurve.diamondAut N (d * d') x = ModularCurve.diamondAut N d (ModularCurve.diamondAut N d' x)) ∧

    ModularCurve.diamondAut N 1 = AlgEquiv.refl ∧

    (∀ d d' : ℕ, d.Coprime N → d'.Coprime N → ((d : ZMod N) * (d' : ZMod N) = 1) →
      ∀ x : ↥(ModularCurve.x1FunctionField N),
        ModularCurve.diamondAut N d (ModularCurve.diamondAut N d' x) = x) ∧

    (∀ d d' : ℕ, d.Coprime N → d'.Coprime N → ((d : ZMod N) = (d' : ZMod N)) →
      ModularCurve.diamondAutBar N d = ModularCurve.diamondAutBar N d') ∧
    (∀ d d' : ℕ, d.Coprime N → d'.Coprime N →
      ∀ x : ↥(ModularCurve.x1FunctionFieldBar N),
        ModularCurve.diamondAutBar N (d * d') x = ModularCurve.diamondAutBar N d (ModularCurve.diamondAutBar N d' x)) ∧
    ModularCurve.diamondAutBar N 1 = AlgEquiv.refl ∧
    (∀ d d' : ℕ, d.Coprime N → d'.Coprime N → ((d : ZMod N) * (d' : ZMod N) = 1) →
      ∀ x : ↥(ModularCurve.x1FunctionFieldBar N),
        ModularCurve.diamondAutBar N d (ModularCurve.diamondAutBar N d' x) = x) := by sorry
